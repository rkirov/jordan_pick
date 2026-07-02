import JordanPick.PicksTheorem.Pick.EarClip

/-!
# Pick's theorem: the assembled reduction (top module)

This capstone file is the top of the split `Pick` development. The bulk of the
proof now lives in the `JordanPick.PicksTheorem.Pick.*` submodules (imported
transitively via `Pick.EarClip`). What remains here is the
`JordanAtMostTwo` section. Lives inside `namespace Pick`.
-/

namespace Pick

open LatticePolygon

variable (P : LatticePolygon)

/-! ### Polygonal Jordan Curve Theorem: `ℝ²∖boundary` has at most two components

Following Erickson's "Jordan Polygon Theorem" (Lemma ≤2): the complement of the
boundary has at most two connected components, proved via the offset tube. We land
the self-contained metric pieces here: nearest-boundary-point existence (compactness)
and the straight-line "reach" lemma that moves any off-boundary point toward the
boundary while staying off it. -/
section JordanAtMostTwo

open LatticePolygon Metric

variable (P : LatticePolygon)

/-- **Boundary is nonempty.** It contains every vertex (the left endpoint of each
edge segment). -/
lemma boundary_nonempty : P.boundary.Nonempty :=
  ⟨toReal (P.vert 0), Set.mem_iUnion.2 ⟨0, left_mem_segment ℝ _ _⟩⟩

/-- **Existence of a nearest boundary point.** For any `q`, the compact nonempty
boundary contains a point `p*` with `dist q p* = infDist q boundary`. -/
lemma exists_nearest_boundary_point (q : ℝ × ℝ) :
    ∃ p ∈ P.boundary, dist q p = Metric.infDist q P.boundary := by
  obtain ⟨p, hp, hpeq⟩ :=
    (boundary_isCompact P).exists_infDist_eq_dist (boundary_nonempty P) q
  exact ⟨p, hp, hpeq.symm⟩

/-- **Travelling toward the nearest boundary point stays off the boundary.**
Let `p* ∈ boundary` realise `dist q p* = infDist q boundary`, and let `q ∉ boundary`.
For `t ∈ [0,1)`, the convex combination `x = (1-t)•q + t•p*` is off the boundary:
every boundary point `b` is at least as far from `q` as `p*`, so
`dist x b ≥ dist q b − dist q x ≥ dist q p* − dist q x = dist x p* > 0`. -/
lemma segment_toward_nearest_off_boundary {q p : ℝ × ℝ} (_ : p ∈ P.boundary)
    (hnear : dist q p = Metric.infDist q P.boundary) (hqb : q ∉ P.boundary)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((1 - t) • q + t • p : ℝ × ℝ) ∉ P.boundary := by
  set x : ℝ × ℝ := (1 - t) • q + t • p with hx
  -- distances from x
  have hxq : dist x q = t * dist q p := by
    rw [hx, dist_eq_norm]
    have : (1 - t) • q + t • p - q = t • (p - q) := by
      module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, dist_eq_norm, ← norm_neg]
    congr 1
    rw [neg_sub]
  have hxp : dist x p = (1 - t) * dist q p := by
    rw [hx, dist_eq_norm]
    have : (1 - t) • q + t • p - p = (1 - t) • (q - p) := by
      module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), dist_eq_norm]
  -- q is at positive distance from boundary
  have hqpos : 0 < dist q p := by
    rw [hnear]
    rw [(boundary_isClosed P).notMem_iff_infDist_pos (boundary_nonempty P)] at hqb
    exact hqb
  intro hxbdry
  -- contradiction: x would be a boundary point, but it is strictly closer than p* allows
  have hxp_pos : 0 < dist x p := by rw [hxp]; positivity
  -- for any boundary point b, dist q b ≥ dist q p
  have hfar : ∀ b ∈ P.boundary, dist q p ≤ dist q b := by
    intro b hb
    rw [hnear]
    exact Metric.infDist_le_dist_of_mem hb
  -- in particular for b = x
  have hqx_far : dist q p ≤ dist q x := hfar x hxbdry
  rw [dist_comm q x, hxq] at hqx_far
  -- dist q p ≤ t * dist q p, impossible since t < 1 and dist q p > 0
  nlinarith [hqpos]

/-- **Feature size** `δ`: the minimum, over all vertex/non-incident-edge pairs, of
`infDist (vert m) (edgeSeg j)`. Implemented as a finite `inf'` over *all* index pairs,
clamping incident pairs (`j = m` or `j = m-1`) to `1` so the term is always positive;
the genuine geometric content is `featureSize_le` below. -/
noncomputable def LatticePolygon.featureSize (P : LatticePolygon) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty (α := ZMod P.n × ZMod P.n))
    (fun mj => if mj.1 ≠ mj.2 ∧ mj.2 ≠ mj.1 - 1
      then Metric.infDist (toReal (P.vert mj.1)) (P.edgeSeg mj.2) else 1)

/-- The **(punctured) offset tube** of radius `ε`: points strictly between the
boundary and distance `ε` from it. -/
def LatticePolygon.Tube (P : LatticePolygon) (ε : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 < Metric.infDist q P.boundary ∧ Metric.infDist q P.boundary < ε}

lemma mem_Tube_iff {ε : ℝ} {q : ℝ × ℝ} :
    q ∈ P.Tube ε ↔ 0 < Metric.infDist q P.boundary ∧ Metric.infDist q P.boundary < ε :=
  Iff.rfl

/-- The tube lies off the boundary. -/
lemma Tube_subset_compl_boundary {ε : ℝ} : P.Tube ε ⊆ P.boundaryᶜ := by
  intro q hq
  rw [Set.mem_compl_iff, (boundary_isClosed P).notMem_iff_infDist_pos (boundary_nonempty P)]
  exact hq.1

/-- **Feature size is positive.** Every term of the defining `inf'` is positive:
incident pairs contribute `1`, non-incident pairs contribute `vertex_infDist_pos`. -/
lemma featureSize_pos (hsimple : P.IsSimple) : 0 < P.featureSize := by
  rw [LatticePolygon.featureSize, Finset.lt_inf'_iff]
  rintro ⟨m, j⟩ _
  by_cases h : m ≠ j ∧ j ≠ m - 1
  · rw [if_pos h]
    exact vertex_infDist_pos P hsimple m j (Ne.symm h.1) h.2
  · rw [if_neg h]; exact one_pos

/-- **Feature size bounds each non-incident vertex/edge distance.** For `j ≠ m`,
`j ≠ m-1`, `featureSize ≤ infDist (vert m) (edgeSeg j)`. -/
lemma featureSize_le (m j : ZMod P.n) (hjm : j ≠ m) (hjm1 : j ≠ m - 1) :
    P.featureSize ≤ Metric.infDist (toReal (P.vert m)) (P.edgeSeg j) := by
  have := Finset.inf'_le
    (f := fun mj : ZMod P.n × ZMod P.n => if mj.1 ≠ mj.2 ∧ mj.2 ≠ mj.1 - 1
      then Metric.infDist (toReal (P.vert mj.1)) (P.edgeSeg mj.2) else 1)
    (Finset.mem_univ (m, j))
  rw [LatticePolygon.featureSize]
  simp only [Ne.symm hjm, hjm1, ne_eq, not_false_eq_true, and_self, if_true] at this
  exact this

/-- **Every off-boundary point reaches the tube.** For `ε > 0`, any `q ∉ boundary`
is `JoinedIn boundaryᶜ` to some point of `Tube ε`. Travel the straight segment from
`q` toward the nearest boundary point `p*` until distance `ε/2`; the whole segment
stays off the boundary (`segment_toward_nearest_off_boundary`), and the endpoint
lands in the tube. -/
lemma reach_tube {ε : ℝ} (hε : 0 < ε) (q : ℝ × ℝ) (hqb : q ∉ P.boundary) :
    ∃ x ∈ P.Tube ε, JoinedIn P.boundaryᶜ q x := by
  obtain ⟨p, hp, hnear⟩ := exists_nearest_boundary_point P q
  set D := Metric.infDist q P.boundary with hD
  have hDpos : 0 < D := by
    rw [hD, ← (boundary_isClosed P).notMem_iff_infDist_pos (boundary_nonempty P)]
    exact hqb
  by_cases hsmall : D < ε
  · -- q already in the tube
    refine ⟨q, ⟨hDpos, hsmall⟩, JoinedIn.refl ?_⟩
    exact Tube_subset_compl_boundary P ⟨hDpos, hsmall⟩
  · -- D ≥ ε; travel to t = 1 - ε/(2D)
    push Not at hsmall
    set t : ℝ := 1 - ε / (2 * D) with ht
    have hDε : ε ≤ D := hsmall
    have ht0 : 0 ≤ t := by
      rw [ht]; rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    have ht1 : t < 1 := by
      rw [ht]; have : 0 < ε / (2 * D) := by positivity
      linarith
    set x : ℝ × ℝ := (1 - t) • q + t • p with hx
    -- distances
    have hxp : dist x p = (1 - t) * D := by
      rw [hx, dist_eq_norm,
        show ((1:ℝ) - t) • q + t • p - p = (1 - t) • (q - p) from by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t),
        ← dist_eq_norm, hnear]
    have hxp_val : dist x p = ε / 2 := by
      rw [hxp, ht]; field_simp; ring
    -- x off boundary
    have hxoff : x ∉ P.boundary :=
      segment_toward_nearest_off_boundary P hp hnear hqb ht0 ht1
    -- infDist x boundary > 0
    have hxpos : 0 < Metric.infDist x P.boundary := by
      rw [← (boundary_isClosed P).notMem_iff_infDist_pos (boundary_nonempty P)]; exact hxoff
    -- infDist x boundary ≤ dist x p = ε/2 < ε
    have hxlt : Metric.infDist x P.boundary < ε := by
      have h1 : Metric.infDist x P.boundary ≤ dist x p := Metric.infDist_le_dist_of_mem hp
      rw [hxp_val] at h1; linarith
    refine ⟨x, ⟨hxpos, hxlt⟩, ?_⟩
    -- the whole segment q → x stays off the boundary
    apply JoinedIn.of_segment_subset
    intro y hy
    rw [Set.mem_compl_iff]
    -- y = (1-s) q + s x = (1 - s t) q + (s t) p for some s ∈ [0,1]
    rw [segment_eq_image] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    simp only [hx]
    have hst0 : 0 ≤ s * t := mul_nonneg hs.1 ht0
    have hst1 : s * t < 1 := by nlinarith [hs.2, ht1, ht0]
    have hrw : (1 - s) • q + s • ((1 - t) • q + t • p) = (1 - s * t) • q + (s * t) • p := by
      module
    rw [hrw]
    exact segment_toward_nearest_off_boundary P hp hnear hqb hst0 hst1

/-- **`q ↦ cross v q` is `ℝ`-linear.** -/
lemma isLinearMap_cross (v : ℝ × ℝ) : IsLinearMap ℝ (fun q : ℝ × ℝ => cross v q) where
  map_add q₁ q₂ := by simp only [cross, Prod.fst_add, Prod.snd_add]; ring
  map_smul c q := by simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **The open "left side" of the line through edge `a → b` is convex.** The set
`{q | 0 < cross (b - a) (q - a)}` (strictly left of the directed line `a → b`) is a
convex open half-plane — the building block for the left strip beside an edge. -/
lemma convex_pos_cross (a b : ℝ × ℝ) :
    Convex ℝ {q : ℝ × ℝ | 0 < cross (b - a) (q - a)} := by
  have hset : {q : ℝ × ℝ | 0 < cross (b - a) (q - a)}
      = {q : ℝ × ℝ | cross (b - a) a < cross (b - a) q} := by
    ext q
    simp only [Set.mem_setOf_eq, cross, Prod.fst_sub, Prod.snd_sub]
    constructor <;> intro h <;> nlinarith [h]
  rw [hset]
  exact convex_halfSpace_gt (isLinearMap_cross (b - a)) (cross (b - a) a)

/-- Symmetrically, the open "right side" `{q | cross (b - a) (q - a) < 0}` is convex. -/
lemma convex_neg_cross (a b : ℝ × ℝ) :
    Convex ℝ {q : ℝ × ℝ | cross (b - a) (q - a) < 0} := by
  have hset : {q : ℝ × ℝ | cross (b - a) (q - a) < 0}
      = {q : ℝ × ℝ | cross (b - a) q < cross (b - a) a} := by
    ext q
    simp only [Set.mem_setOf_eq, cross, Prod.fst_sub, Prod.snd_sub]
    constructor <;> intro h <;> nlinarith [h]
  rw [hset]
  exact convex_halfSpace_lt (isLinearMap_cross (b - a)) (cross (b - a) a)

/-- **The left strip beside a single edge is convex (hence preconnected).** For edge
`i` (from `a = vert i` to `b = vert (i+1)`), the set of points lying strictly to the
left of the directed line and within the open `ε`-thickening of the edge segment,
`{q | 0 < cross (b - a) (q - a)} ∩ thickening ε (edgeSeg i)`, is convex: it is the
intersection of the convex left half-plane (`convex_pos_cross`) with the convex
thickening of the (convex) segment (`Convex.thickening`). This is the single-edge
left-strip connectivity, the per-edge piece of the tube-half induction. -/
lemma convex_left_strip (i : ZMod P.n) (ε : ℝ) :
    Convex ℝ ({q : ℝ × ℝ | 0 < cross (toReal (P.vert (i + 1)) - toReal (P.vert i))
        (q - toReal (P.vert i))} ∩ Metric.thickening ε (P.edgeSeg i)) := by
  refine (convex_pos_cross _ _).inter ?_
  exact (convex_segment _ _).thickening ε

/-- **The right strip beside a single edge is convex (hence preconnected).** -/
lemma convex_right_strip (i : ZMod P.n) (ε : ℝ) :
    Convex ℝ ({q : ℝ × ℝ | cross (toReal (P.vert (i + 1)) - toReal (P.vert i))
        (q - toReal (P.vert i)) < 0} ∩ Metric.thickening ε (P.edgeSeg i)) := by
  refine (convex_neg_cross _ _).inter ?_
  exact (convex_segment _ _).thickening ε

/-! ### The left / right strips and their union -/

/-- **The left strip beside edge `i`.** Points strictly to the left of the directed
line `vert i → vert (i+1)` and within the open `ε`-thickening of edge `i`. -/
def LatticePolygon.leftStrip (i : ZMod P.n) (ε : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | 0 < cross (toReal (P.vert (i + 1)) - toReal (P.vert i))
      (q - toReal (P.vert i))} ∩ Metric.thickening ε (P.edgeSeg i)

/-- **The right strip beside edge `i`.** Strictly to the right of the directed line,
within the `ε`-thickening of edge `i`. -/
def LatticePolygon.rightStrip (i : ZMod P.n) (ε : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | cross (toReal (P.vert (i + 1)) - toReal (P.vert i))
      (q - toReal (P.vert i)) < 0} ∩ Metric.thickening ε (P.edgeSeg i)

/-! ### Explicit left/right offset rectangles (Erickson nearest-point decomposition)

The thickening-strip cover failed at corners. We instead build the offset cover from
*parametrized* pieces so that path-connectivity is a clean continuous-image argument.
For edge `i` from `a = vert i` to `b = vert (i+1)`, with direction `d = b - a`, the
**unit left normal** is `nL i = ‖d‖⁻¹ • (-d₂, d₁)`. The **left rectangle** beside the
edge is the affine-parametrized open rectangle
`{(1-s)•a + s•b + t•nL : s∈(0,1), t∈(0,ε)}`. -/

/-- The direction vector of edge `i`: `vert (i+1) - vert i`. -/
def LatticePolygon.edgeDir (i : ZMod P.n) : ℝ × ℝ :=
  toReal (P.vert (i + 1)) - toReal (P.vert i)

/-- The **unit left normal** to edge `i` (90° CCW from the edge direction, normalized). -/
noncomputable def LatticePolygon.leftNormal (i : ZMod P.n) : ℝ × ℝ :=
  ‖P.edgeDir i‖⁻¹ • (-(P.edgeDir i).2, (P.edgeDir i).1)

/-- The **unit right normal** to edge `i` (the negation of the left normal). -/
noncomputable def LatticePolygon.rightNormal (i : ZMod P.n) : ℝ × ℝ :=
  ‖P.edgeDir i‖⁻¹ • ((P.edgeDir i).2, -(P.edgeDir i).1)

/-- The affine parametrization of the strip beside edge `i` with normal `nrm`:
`(s,t) ↦ (1-s)•a + s•b + t•nrm`. -/
def LatticePolygon.rectMap (i : ZMod P.n) (nrm : ℝ × ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun st => (1 - st.1) • toReal (P.vert i) + st.1 • toReal (P.vert (i + 1)) + st.2 • nrm

/-- The **left rectangle** beside edge `i`: the open parallelogram of points at signed
left-offset `t ∈ (0,ε)` over the open edge `s ∈ (0,1)`. -/
noncomputable def LatticePolygon.leftRect (i : ZMod P.n) (ε : ℝ) : Set (ℝ × ℝ) :=
  P.rectMap i (P.leftNormal i) '' (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) ε)

/-- The **right rectangle** beside edge `i`. -/
noncomputable def LatticePolygon.rightRect (i : ZMod P.n) (ε : ℝ) : Set (ℝ × ℝ) :=
  P.rectMap i (P.rightNormal i) '' (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) ε)

/-- `rectMap` is continuous (a polynomial in its two real arguments). -/
lemma continuous_rectMap (i : ZMod P.n) (nrm : ℝ × ℝ) : Continuous (P.rectMap i nrm) := by
  unfold LatticePolygon.rectMap; fun_prop

/-- **Each offset rectangle is path-connected**, being the continuous image of the
convex (hence path-connected) parameter box `Ioo 0 1 ×ˢ Ioo 0 ε`. -/
lemma isPathConnected_rect (i : ZMod P.n) (nrm : ℝ × ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (P.rectMap i nrm '' (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) ε)) := by
  apply IsPathConnected.image
  · apply Convex.isPathConnected ((convex_Ioo 0 1).prod (convex_Ioo 0 ε))
    exact ⟨(1 / 2, ε / 2), ⟨by norm_num, by norm_num⟩, by simp; linarith, by simp; linarith⟩
  · exact continuous_rectMap P i nrm

/-- **Edges are nondegenerate**: `edgeDir i ≠ 0` for a simple polygon. -/
lemma edgeDir_ne_zero (hsimple : P.IsSimple) (i : ZMod P.n) : P.edgeDir i ≠ 0 := by
  rw [LatticePolygon.edgeDir, sub_ne_zero]
  exact fun h => hsimple.1 i (toReal_injective h.symm)

/-- The squared coordinate norm of a nonzero edge direction is positive. -/
lemma normSq_edgeDir_pos (hsimple : P.IsSimple) (i : ZMod P.n) :
    0 < (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 := by
  have h : (P.edgeDir i).1 ≠ 0 ∨ (P.edgeDir i).2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact edgeDir_ne_zero P hsimple i (Prod.ext hc.1 hc.2)
  rcases h with h | h
  · have : (P.edgeDir i).1 ^ 2 > 0 := by positivity
    nlinarith [sq_nonneg (P.edgeDir i).2]
  · have : (P.edgeDir i).2 ^ 2 > 0 := by positivity
    nlinarith [sq_nonneg (P.edgeDir i).1]

/-- **Consecutive edges are not antiparallel.** There is no `μ > 0` with
`edgeDir (i+1) = (-μ) • edgeDir i`. If there were, then a point `p = b + λ•(a - b)`
just past the shared vertex `b = vert (i+1)` toward `a = vert i` (for small `λ ∈ (0,μ]`,
`λ < 1`) would lie on *both* `edgeSeg i` (segment `a → b`) and `edgeSeg (i+1)`
(segment `b → c` with `c = b - μ•(b-a) = b + μ•(a-b)`). Since `p ≠ b`, this enlarges
`edgeSeg i ∩ edgeSeg (i+1)` beyond `{b}`, contradicting `IsSimple` clause 3. -/
lemma edgeDir_not_antiparallel (hsimple : P.IsSimple) (i : ZMod P.n) :
    ¬ ∃ μ : ℝ, 0 < μ ∧ P.edgeDir (i + 1) = (-μ) • P.edgeDir i := by
  rintro ⟨μ, hμ, heq⟩
  set a := toReal (P.vert i) with ha
  set b := toReal (P.vert (i + 1)) with hb
  set c := toReal (P.vert (i + 1 + 1)) with hc
  -- `edgeDir (i+1) = c - b`, `edgeDir i = b - a`, so `c - b = -μ • (b - a)`.
  have hcb : c - b = (-μ) • (b - a) := by
    have e1 : P.edgeDir (i + 1) = c - b := by
      rw [LatticePolygon.edgeDir]
    have e2 : P.edgeDir i = b - a := by
      rw [LatticePolygon.edgeDir]
    rw [e1, e2] at heq; exact heq
  set lam : ℝ := min μ 1 / 2 with hlamdef
  have hlampos : 0 < lam := by positivity
  have hlamlt1 : lam < 1 := by
    have : min μ 1 ≤ 1 := min_le_right _ _
    simp only [hlamdef]; linarith
  have hlamleμ : lam ≤ μ := by
    have : min μ 1 ≤ μ := min_le_left _ _
    simp only [hlamdef]; linarith
  -- the overlap witness
  set p : ℝ × ℝ := b + lam • (a - b) with hp
  -- p ∈ edgeSeg i (the segment a → b)
  have hpi : p ∈ P.edgeSeg i := by
    rw [LatticePolygon.edgeSeg, ← ha, ← hb, segment_eq_image]
    refine ⟨1 - lam, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hp]; module
  -- p ∈ edgeSeg (i+1) (the segment b → c); with s = lam/μ ∈ (0,1]
  have hpi1 : p ∈ P.edgeSeg (i + 1) := by
    rw [LatticePolygon.edgeSeg, ← hb, ← hc, segment_eq_image]
    refine ⟨lam / μ, ⟨by positivity, by rw [div_le_one hμ]; exact hlamleμ⟩, ?_⟩
    have hcbb : c = b + μ • (a - b) := by
      have hh : c = b + (-μ) • (b - a) := by rw [← hcb]; abel
      rw [hh]; module
    simp only [hp, hcbb]
    rw [show (1 - lam / μ) • b + (lam / μ) • (b + μ • (a - b))
          = b + (lam / μ * μ) • (a - b) from by module,
      div_mul_cancel₀ lam (ne_of_gt hμ)]
  -- both ⟹ p ∈ {b}, but p ≠ b
  have hcap : p ∈ P.edgeSeg i ∩ P.edgeSeg (i + 1) := ⟨hpi, hpi1⟩
  rw [hsimple.2.2 i, ← hb] at hcap
  -- p = b would force lam • (a - b) = 0, but lam > 0 and a ≠ b
  rw [Set.mem_singleton_iff, hp] at hcap
  have hab : a ≠ b := by
    rw [ha, hb]; intro h; exact hsimple.1 i (toReal_injective h)
  have : lam • (a - b) = 0 := by
    have := hcap
    rw [add_eq_left] at this; exact this
  rw [smul_eq_zero] at this
  rcases this with h | h
  · exact (ne_of_gt hlampos) h
  · exact hab (by rw [sub_eq_zero] at h; exact h)

/-- **Euclidean Cauchy-Schwarz with the antiparallel equality case excluded.**
For nonzero `d₁, d₂ : ℝ × ℝ` that are not antiparallel (no `μ > 0` with `d₂ = (-μ)•d₁`),
the Euclidean inner product strictly exceeds `-‖d₁‖_E‖d₂‖_E`, i.e.
`0 < √(d₁.1²+d₁.2²)·√(d₂.1²+d₂.2²) + (d₁.1 d₂.1 + d₁.2 d₂.2)`.
Equality in Cauchy-Schwarz (`ip² = N₁N₂ ⟺ cross = 0`) with `ip ≤ 0` forces antiparallel. -/
lemma eNorm_mul_add_inner_pos {d₁ d₂ : ℝ × ℝ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hanti : ¬ ∃ μ : ℝ, 0 < μ ∧ d₂ = (-μ) • d₁) :
    0 < Real.sqrt (d₁.1 ^ 2 + d₁.2 ^ 2) * Real.sqrt (d₂.1 ^ 2 + d₂.2 ^ 2)
        + (d₁.1 * d₂.1 + d₁.2 * d₂.2) := by
  set N₁ : ℝ := d₁.1 ^ 2 + d₁.2 ^ 2 with hN₁
  set N₂ : ℝ := d₂.1 ^ 2 + d₂.2 ^ 2 with hN₂
  set ip : ℝ := d₁.1 * d₂.1 + d₁.2 * d₂.2 with hip
  have hor₁ : d₁.1 ≠ 0 ∨ d₁.2 ≠ 0 := by
    by_contra hc; push Not at hc; exact hd₁ (Prod.ext hc.1 hc.2)
  have hor₂ : d₂.1 ≠ 0 ∨ d₂.2 ≠ 0 := by
    by_contra hc; push Not at hc; exact hd₂ (Prod.ext hc.1 hc.2)
  have hN₁pos : 0 < N₁ := by
    rcases hor₁ with h | h
    · have : d₁.1 ^ 2 > 0 := by positivity
      simp only [hN₁]; nlinarith [sq_nonneg d₁.2]
    · have : d₁.2 ^ 2 > 0 := by positivity
      simp only [hN₁]; nlinarith [sq_nonneg d₁.1]
  have hN₂pos : 0 < N₂ := by
    rcases hor₂ with h | h
    · have : d₂.1 ^ 2 > 0 := by positivity
      simp only [hN₂]; nlinarith [sq_nonneg d₂.2]
    · have : d₂.2 ^ 2 > 0 := by positivity
      simp only [hN₂]; nlinarith [sq_nonneg d₂.1]
  set e₁ : ℝ := Real.sqrt N₁ with he₁
  set e₂ : ℝ := Real.sqrt N₂ with he₂
  have he₁sq : e₁ ^ 2 = N₁ := by rw [he₁, sq, Real.mul_self_sqrt hN₁pos.le]
  have he₂sq : e₂ ^ 2 = N₂ := by rw [he₂, sq, Real.mul_self_sqrt hN₂pos.le]
  have he₁pos : 0 < e₁ := Real.sqrt_pos.mpr hN₁pos
  have he₂pos : 0 < e₂ := Real.sqrt_pos.mpr hN₂pos
  by_contra hle
  push Not at hle
  -- hle : e₁ * e₂ + ip ≤ 0, so ip ≤ -e₁e₂ ≤ 0 and ip² ≥ e₁²e₂² = N₁N₂
  have hip_nonpos : ip ≤ - (e₁ * e₂) := by linarith
  have hee_nonneg : 0 ≤ e₁ * e₂ := by positivity
  have hip2 : N₁ * N₂ ≤ ip ^ 2 := by nlinarith [he₁sq, he₂sq, hip_nonpos, hee_nonneg]
  -- Cauchy-Schwarz: N₁ N₂ - ip² = cross² ≥ 0
  have hcross_sq : N₁ * N₂ - ip ^ 2 = (d₁.1 * d₂.2 - d₁.2 * d₂.1) ^ 2 := by
    simp only [hN₁, hN₂, hip]; ring
  have hcross0 : d₁.1 * d₂.2 - d₁.2 * d₂.1 = 0 := by
    nlinarith [sq_nonneg (d₁.1 * d₂.2 - d₁.2 * d₂.1), hip2, hcross_sq]
  -- parallel decomposition from cross = 0
  have hpar1 : N₁ * d₂.1 = ip * d₁.1 := by simp only [hN₁, hip]; nlinarith [hcross0]
  have hpar2 : N₁ * d₂.2 = ip * d₁.2 := by simp only [hN₁, hip]; nlinarith [hcross0]
  have hip_neg : ip < 0 := by
    have hip_nonpos' : ip ≤ 0 := le_trans hip_nonpos (by linarith [hee_nonneg])
    rcases lt_or_eq_of_le hip_nonpos' with h | h
    · exact h
    · -- ip = 0 with cross = 0 and d₁ ≠ 0 ⟹ d₂ = 0, contradiction
      exfalso; apply hd₂
      have hd2_1 : d₂.1 = 0 := by
        have hh := hpar1; rw [h, zero_mul] at hh
        rcases mul_eq_zero.mp hh with h' | h'
        · exact absurd h' (ne_of_gt hN₁pos)
        · exact h'
      have hd2_2 : d₂.2 = 0 := by
        have hh := hpar2; rw [h, zero_mul] at hh
        rcases mul_eq_zero.mp hh with h' | h'
        · exact absurd h' (ne_of_gt hN₁pos)
        · exact h'
      exact Prod.ext hd2_1 hd2_2
  -- antiparallel: d₂ = (ip/N₁) • d₁ with ip/N₁ < 0
  apply hanti
  refine ⟨- (ip / N₁), neg_pos.mpr (div_neg_of_neg_of_pos hip_neg hN₁pos), ?_⟩
  have hd2_1 : d₂.1 = (ip / N₁) * d₁.1 := by
    rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hN₁pos)]; linarith [hpar1]
  have hd2_2 : d₂.2 = (ip / N₁) * d₁.2 := by
    rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hN₁pos)]; linarith [hpar2]
  apply Prod.ext
  · simp only [Prod.smul_fst, smul_eq_mul, neg_mul]; rw [hd2_1]; ring
  · simp only [Prod.smul_snd, smul_eq_mul, neg_mul]; rw [hd2_2]; ring

/-- **The common left-cone of two consecutive edges is nonempty.** There is a direction
`u` strictly to the left of *both* `edgeDir i` and `edgeDir (i+1)`
(`0 < cross (edgeDir i) u` and `0 < cross (edgeDir (i+1)) u`). Witness:
`u = ‖d₂‖_E • (-d₁.2, d₁.1) + ‖d₁‖_E • (-d₂.2, d₂.1)`, the sum of the two (Euclidean-)
scaled left-normals; both cross products reduce to `‖dₖ‖_E · (‖d₁‖_E‖d₂‖_E + ⟪d₁,d₂⟫) > 0`
via `eNorm_mul_add_inner_pos` (the not-antiparallel Cauchy-Schwarz bound). -/
lemma exists_dir_left_of_both (hsimple : P.IsSimple) (i : ZMod P.n) :
    ∃ u : ℝ × ℝ, 0 < cross (P.edgeDir i) u ∧ 0 < cross (P.edgeDir (i + 1)) u := by
  set d₁ := P.edgeDir i with hd₁def
  set d₂ := P.edgeDir (i + 1) with hd₂def
  have hd₁ : d₁ ≠ 0 := edgeDir_ne_zero P hsimple i
  have hd₂ : d₂ ≠ 0 := edgeDir_ne_zero P hsimple (i + 1)
  have hanti : ¬ ∃ μ : ℝ, 0 < μ ∧ d₂ = (-μ) • d₁ :=
    edgeDir_not_antiparallel P hsimple i
  set e₁ : ℝ := Real.sqrt (d₁.1 ^ 2 + d₁.2 ^ 2) with he₁
  set e₂ : ℝ := Real.sqrt (d₂.1 ^ 2 + d₂.2 ^ 2) with he₂
  have hkey : 0 < e₁ * e₂ + (d₁.1 * d₂.1 + d₁.2 * d₂.2) :=
    eNorm_mul_add_inner_pos hd₁ hd₂ hanti
  have he₁nn : 0 ≤ e₁ := Real.sqrt_nonneg _
  have he₂nn : 0 ≤ e₂ := Real.sqrt_nonneg _
  have he₁sq : e₁ ^ 2 = d₁.1 ^ 2 + d₁.2 ^ 2 := by
    rw [he₁, sq, Real.mul_self_sqrt (by positivity)]
  have he₂sq : e₂ ^ 2 = d₂.1 ^ 2 + d₂.2 ^ 2 := by
    rw [he₂, sq, Real.mul_self_sqrt (by positivity)]
  refine ⟨e₂ • (-d₁.2, d₁.1) + e₁ • (-d₂.2, d₂.1), ?_, ?_⟩
  · have : cross d₁ (e₂ • (-d₁.2, d₁.1) + e₁ • (-d₂.2, d₂.1))
        = e₁ * (e₁ * e₂ + (d₁.1 * d₂.1 + d₁.2 * d₂.2)) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      nlinarith [he₁sq]
    rw [this]
    have he₁pos : 0 < e₁ := Real.sqrt_pos.mpr (by
      rcases (by by_contra hc; push Not at hc; exact hd₁ (Prod.ext hc.1 hc.2) :
        d₁.1 ≠ 0 ∨ d₁.2 ≠ 0) with h | h
      · nlinarith [sq_nonneg d₁.2, sq_pos_of_ne_zero h]
      · nlinarith [sq_nonneg d₁.1, sq_pos_of_ne_zero h])
    positivity
  · have : cross d₂ (e₂ • (-d₁.2, d₁.1) + e₁ • (-d₂.2, d₂.1))
        = e₂ * (e₁ * e₂ + (d₁.1 * d₂.1 + d₁.2 * d₂.2)) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      nlinarith [he₂sq]
    rw [this]
    have he₂pos : 0 < e₂ := Real.sqrt_pos.mpr (by
      rcases (by by_contra hc; push Not at hc; exact hd₂ (Prod.ext hc.1 hc.2) :
        d₂.1 ≠ 0 ∨ d₂.2 ≠ 0) with h | h
      · nlinarith [sq_nonneg d₂.2, sq_pos_of_ne_zero h]
      · nlinarith [sq_nonneg d₂.1, sq_pos_of_ne_zero h])
    positivity

/-- **The common right-cone of two consecutive edges is nonempty.** Mirror of
`exists_dir_left_of_both`: a direction `u` strictly to the right of both edges
(`cross (edgeDir i) u < 0` and `cross (edgeDir (i+1)) u < 0`). Witness is the negation
of the left-cone witness. -/
lemma exists_dir_right_of_both (hsimple : P.IsSimple) (i : ZMod P.n) :
    ∃ u : ℝ × ℝ, cross (P.edgeDir i) u < 0 ∧ cross (P.edgeDir (i + 1)) u < 0 := by
  obtain ⟨u, hu1, hu2⟩ := exists_dir_left_of_both P hsimple i
  refine ⟨-u, ?_, ?_⟩
  · have : cross (P.edgeDir i) (-u) = - cross (P.edgeDir i) u := by
      simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; linarith
  · have : cross (P.edgeDir (i + 1)) (-u) = - cross (P.edgeDir (i + 1)) u := by
      simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; linarith

/-- **`leftRect` lands strictly to the left of edge `i`'s directed line.** The cross
product `cross (edgeDir i) (q - vert i) = t·‖d‖⁻¹·(d₁²+d₂²) > 0` for the offset
parameter `t > 0` (norm-agnostic: only the sign matters). This is the side-determining
fact tying `leftRect` to the existing `leftStrip` half-plane condition. -/
lemma leftRect_cross_pos (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ P.leftRect i ε) :
    0 < cross (P.edgeDir i) (q - toReal (P.vert i)) := by
  obtain ⟨⟨s, t⟩, ⟨_, ht0, _⟩, rfl⟩ := hq
  have hcross : cross (P.edgeDir i) (P.rectMap i (P.leftNormal i) (s, t) - toReal (P.vert i))
      = t * (‖P.edgeDir i‖⁻¹ * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2)) := by
    simp only [LatticePolygon.rectMap, LatticePolygon.leftNormal, cross, LatticePolygon.edgeDir,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul]
    ring
  rw [hcross]
  have hnorm : 0 < ‖P.edgeDir i‖⁻¹ := by
    rw [inv_pos, norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have := normSq_edgeDir_pos P hsimple i
  positivity

/-- **`rightRect` lands strictly to the right of edge `i`'s directed line.** -/
lemma rightRect_cross_neg (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ P.rightRect i ε) :
    cross (P.edgeDir i) (q - toReal (P.vert i)) < 0 := by
  obtain ⟨⟨s, t⟩, ⟨_, ht0, _⟩, rfl⟩ := hq
  have hcross : cross (P.edgeDir i) (P.rectMap i (P.rightNormal i) (s, t) - toReal (P.vert i))
      = -(t * (‖P.edgeDir i‖⁻¹ * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2))) := by
    simp only [LatticePolygon.rectMap, LatticePolygon.rightNormal, cross, LatticePolygon.edgeDir,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul]
    ring
  rw [hcross]
  have hnorm : 0 < ‖P.edgeDir i‖⁻¹ := by
    rw [inv_pos, norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have := normSq_edgeDir_pos P hsimple i
  have : 0 < t * (‖P.edgeDir i‖⁻¹ * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2)) := by positivity
  linarith

/-- **The left half `L`** of the offset tube: the union of all left strips. -/
def LatticePolygon.leftTube (ε : ℝ) : Set (ℝ × ℝ) := ⋃ i, P.leftStrip i ε

/-- **The right half `R`** of the offset tube: the union of all right strips. -/
def LatticePolygon.rightTube (ε : ℝ) : Set (ℝ × ℝ) := ⋃ i, P.rightStrip i ε

/-- **Path-connected union along a `reflTransGen` chain of meeting pieces.**
The path-connected analogue of `IsConnected.iUnion_of_reflTransGen` (Mathlib only has
the `IsConnected`/`IsPreconnected` versions). If every piece `s i` is path-connected and
the "meet" relation `(s i ∩ s j).Nonempty` reflexive-transitively connects all indices,
then `⋃ i, s i` is path-connected. Paths compose through the shared meeting points. -/
theorem isPathConnected_iUnion_of_reflTransGen {ι : Type*} [Nonempty ι]
    {s : ι → Set (ℝ × ℝ)} (hs : ∀ i, IsPathConnected (s i))
    (hchain : ∀ i j, Relation.ReflTransGen (fun i j => (s i ∩ s j).Nonempty) i j) :
    IsPathConnected (⋃ i, s i) := by
  classical
  inhabit ι
  -- basepoint in s default
  obtain ⟨b, hb⟩ := (hs default).nonempty
  refine ⟨b, Set.mem_iUnion.2 ⟨default, hb⟩, ?_⟩
  -- every point of the union joins to b
  rintro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨j, hj⟩ := hy
  -- it suffices to join b to any point of s j; do it by induction on the chain default → j
  have key : ∀ k, Relation.ReflTransGen (fun i j => (s i ∩ s j).Nonempty) default k →
      ∀ z ∈ s k, JoinedIn (⋃ i, s i) b z := by
    intro k hk
    induction hk with
    | refl =>
      intro z hz
      exact ((hs default).joinedIn b hb z hz).mono (Set.subset_iUnion s default)
    | @tail c d hcd hmeet ih =>
      intro z hz
      obtain ⟨w, hwc, hwd⟩ := hmeet
      -- b → w (w ∈ s c) by ih, then w → z (both in s d)
      refine (ih w hwc).trans ?_
      exact ((hs d).joinedIn w hwd z hz).mono (Set.subset_iUnion s d)
  exact key j (hchain default j) y hj

/-- **Reduction: a two-piece path-connected cover of the tube yields a two-piece
preconnected cover of `boundaryᶜ`.** If the tube `Tube ε` is covered by two
path-connected sets `L`, `R`, then `boundaryᶜ` is the union of the two path
components `pathComponentIn boundaryᶜ l₀` and `pathComponentIn boundaryᶜ r₀`
(`l₀ ∈ L`, `r₀ ∈ R`), each preconnected. This is the non-circular conclusion of the
offset-tube argument: every off-boundary point reaches the tube (`reach_tube`), hence
lies in the path component of one of the two anchors. -/
lemma compl_boundary_atMost_two_of_tube_cover {ε : ℝ} (hε : 0 < ε)
    {L R : Set (ℝ × ℝ)} (hcover : P.Tube ε ⊆ L ∪ R)
    (hLsub : L ⊆ P.boundaryᶜ) (hRsub : R ⊆ P.boundaryᶜ)
    (hLpc : IsPathConnected L) (hRpc : IsPathConnected R) :
    ∃ A B : Set (ℝ × ℝ), A ∪ B = P.boundaryᶜ ∧ IsPreconnected A ∧ IsPreconnected B := by
  obtain ⟨l₀, hl₀⟩ := hLpc.nonempty
  obtain ⟨r₀, hr₀⟩ := hRpc.nonempty
  refine ⟨pathComponentIn P.boundaryᶜ l₀, pathComponentIn P.boundaryᶜ r₀, ?_, ?_, ?_⟩
  · -- the union is exactly boundaryᶜ
    apply Set.Subset.antisymm
    · -- each path component sits inside boundaryᶜ
      apply Set.union_subset <;> exact pathComponentIn_subset
    · -- every off-boundary point reaches the tube, hence one of the two components
      intro q hq
      simp only [Set.mem_compl_iff] at hq
      obtain ⟨x, hxtube, hjoin⟩ := reach_tube P hε q hq
      -- x is in L or R
      rcases hcover hxtube with hxL | hxR
      · -- x ∈ L; L lies in l₀'s path component, so q joins to l₀
        left
        have hxin : x ∈ pathComponentIn P.boundaryᶜ l₀ :=
          hLpc.subset_pathComponentIn hl₀ hLsub hxL
        -- JoinedIn boundaryᶜ l₀ x and JoinedIn boundaryᶜ q x ⟹ JoinedIn boundaryᶜ l₀ q
        exact (hxin.trans hjoin.symm)
      · right
        have hxin : x ∈ pathComponentIn P.boundaryᶜ r₀ :=
          hRpc.subset_pathComponentIn hr₀ hRsub hxR
        exact (hxin.trans hjoin.symm)
  · exact (isPathConnected_pathComponentIn (hLsub hl₀)).isConnected.isPreconnected
  · exact (isPathConnected_pathComponentIn (hRsub hr₀)).isConnected.isPreconnected

/-! ### A reusable tool: regions under a positive continuous graph are path-connected

The corner-truncated offset regions of the tube cover are not parallelograms but
"regions under a graph": over a path-connected base `B ⊆ X` with a positive continuous
height function `f : X → ℝ`, the set `{(b,t) | b ∈ B, 0 < t < f b}` (and its continuous
image) is path-connected. Any two points are joined by a comb path: drop both to a
common small height `ε'` (below the minimum of `f` along a connecting path in `B`),
slide horizontally along `B × {ε'}`, then rise. -/

/-- **The parameter region under a positive continuous graph is path-connected.**
For a path-connected base `B ⊆ X` and a continuous `f : X → ℝ` positive on `B`, the
set `{(b,t) | b ∈ B, 0 < t < f b}` is path-connected. -/
lemma isPathConnected_graphParamRegion {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : IsPathConnected B) {f : X → ℝ} (hf : Continuous f)
    (hfpos : ∀ b ∈ B, 0 < f b) :
    IsPathConnected {p : X × ℝ | p.1 ∈ B ∧ 0 < p.2 ∧ p.2 < f p.1} := by
  set R := {p : X × ℝ | p.1 ∈ B ∧ 0 < p.2 ∧ p.2 < f p.1} with hR
  -- A "vertical" join: at a fixed base `b ∈ B`, any two heights in `(0, f b)` are joined.
  have vert : ∀ b ∈ B, ∀ h₀ h₁ : ℝ, 0 < h₀ → h₀ < f b → 0 < h₁ → h₁ < f b →
      JoinedIn R (b, h₀) (b, h₁) := by
    intro b hb h₀ h₁ hh₀0 hh₀1 hh₁0 hh₁1
    refine JoinedIn.ofLine (f := fun t => (b, (1 - t) * h₀ + t * h₁)) ?_ (by simp) (by simp) ?_
    · fun_prop
    · rintro _ ⟨t, ht, rfl⟩
      simp only [hR, Set.mem_setOf_eq]
      refine ⟨hb, ?_, ?_⟩
      · nlinarith [ht.1, ht.2, mul_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) hh₀0.le,
          mul_nonneg ht.1 hh₁0.le]
      · rcases eq_or_lt_of_le ht.2 with ht1 | ht1
        · subst ht1; simpa using hh₁1
        · nlinarith [mul_pos (by linarith [ht.2] : (0:ℝ) < 1 - t) (by linarith : (0:ℝ) < f b - h₀),
            mul_nonneg ht.1 (by linarith : (0:ℝ) ≤ f b - h₁)]
  obtain ⟨b₀, hb₀⟩ := hB.nonempty
  refine ⟨(b₀, f b₀ / 2),
    ⟨hb₀, by have := hfpos b₀ hb₀; linarith, by have := hfpos b₀ hb₀; linarith⟩, ?_⟩
  rintro ⟨b, h⟩ ⟨hbB, hh0, hh1⟩
  -- path γ in B from b₀ to b; f has a positive minimum m along its compact image
  have hjoin : JoinedIn B b₀ b := hB.joinedIn b₀ hb₀ b hbB
  set γ := hjoin.somePath with hγ
  have hcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
  obtain ⟨x₀, hx₀mem, hmin⟩ := hcompact.exists_isMinOn (Set.range_nonempty γ) hf.continuousOn
  set m := f x₀ with hm
  have hrng : Set.range γ ⊆ B := by rintro _ ⟨t, rfl⟩; exact hjoin.somePath_mem t
  have hmpos : 0 < m := hfpos x₀ (hrng hx₀mem)
  have hmle : ∀ t, m ≤ f (γ t) := fun t => hmin (Set.mem_range_self t)
  -- the common small height ε'
  set ε' := min m (min h (f b)) / 2 with hε'
  have hfb := hfpos b hbB
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have hε'lt_m : ε' < m := by
    rw [hε']; linarith [min_le_left m (min h (f b))]
  have hε'lt_h : ε' < h := by
    rw [hε']; linarith [le_trans (min_le_right m (min h (f b))) (min_le_left h (f b))]
  have hε'lt_fb : ε' < f b := by
    rw [hε']; linarith [le_trans (min_le_right m (min h (f b))) (min_le_right h (f b))]
  -- drop at b₀ to height ε'
  have hfb₀ := hfpos b₀ hb₀
  have step1 : JoinedIn R (b₀, f b₀ / 2) (b₀, ε') := by
    refine vert b₀ hb₀ _ _ (by linarith) (by linarith) hε'pos ?_
    have h2 : m ≤ f (γ 0) := hmle 0
    rw [γ.source] at h2; linarith
  -- slide along γ at height ε'
  have step2 : JoinedIn R (b₀, ε') (b, ε') := by
    refine ⟨γ.prod (Path.refl ε'), ?_⟩
    intro t
    rw [Path.prod_coe]
    refine ⟨hrng (Set.mem_range_self t), hε'pos, ?_⟩
    have := hmle t
    simp only [Path.refl_apply]; linarith
  -- rise at b to height h
  have step3 : JoinedIn R (b, ε') (b, h) :=
    vert b hbB _ _ hε'pos hε'lt_fb hh0 hh1
  exact (step1.trans step2).trans step3

/-- **Region under a positive continuous graph is path-connected.** For a
path-connected base `B ⊆ X`, a continuous `f : X → ℝ` positive on `B`, and a continuous
`g : X × ℝ → Y`, the image region `{g (b,t) | b ∈ B, 0 < t < f b}` is path-connected.
This is the reusable tool for the corner-truncated offset regions of the tube cover. -/
lemma isPathConnected_graphRegion {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {B : Set X} (hB : IsPathConnected B) {f : X → ℝ} (hf : Continuous f)
    (hfpos : ∀ b ∈ B, 0 < f b) {g : X × ℝ → Y} (hg : Continuous g) :
    IsPathConnected (g '' {p : X × ℝ | p.1 ∈ B ∧ 0 < p.2 ∧ p.2 < f p.1}) :=
  (isPathConnected_graphParamRegion hB hf hfpos).image hg

/-! ### Edge clearance: a uniform separation radius for non-adjacent edges -/

/-- **Edge clearance.** A single positive radius `r` such that every pair of
*non-adjacent* edges (`i ≠ j`, `i+1 ≠ j`, `j+1 ≠ i`) keeps distance `≥ r` at every
pair of points. Obtained by taking the finite `inf'` over all index pairs of the
per-pair separation radius (`edges_uniformly_separated`), clamping adjacent/equal
pairs to `1`. This is the geometric clearance that lets a thin offset rectangle of
radius `< r` avoid every non-adjacent edge. -/
lemma edgeClearance_pos (hsimple : P.IsSimple) :
    ∃ r > 0, ∀ i j : ZMod P.n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      ∀ x ∈ P.edgeSeg i, ∀ x' ∈ P.edgeSeg j, r ≤ dist x x' := by
  classical
  set g : ZMod P.n × ZMod P.n → ℝ := fun ij =>
    if h : ij.1 ≠ ij.2 ∧ ij.1 + 1 ≠ ij.2 ∧ ij.2 + 1 ≠ ij.1
    then (edges_uniformly_separated P hsimple ij.1 ij.2 h.1 h.2.1 h.2.2).choose
    else 1 with hg
  refine ⟨Finset.univ.inf' (Finset.univ_nonempty (α := ZMod P.n × ZMod P.n)) g, ?_, ?_⟩
  · rw [gt_iff_lt, Finset.lt_inf'_iff]
    rintro ⟨i, j⟩ _
    by_cases h : i ≠ j ∧ i + 1 ≠ j ∧ j + 1 ≠ i
    · simp only [hg]; rw [dif_pos h]
      exact (edges_uniformly_separated P hsimple i j h.1 h.2.1 h.2.2).choose_spec.1
    · simp only [hg]; rw [dif_neg h]; exact one_pos
  · intro i j hij hij1 hji1 x hx x' hx'
    have hle := Finset.inf'_le g (Finset.mem_univ (i, j))
    have hpos : g (i, j) = (edges_uniformly_separated P hsimple i j hij hij1 hji1).choose := by
      simp only [hg]; rw [dif_pos (And.intro hij (And.intro hij1 hji1))]
    rw [hpos] at hle
    exact le_trans hle ((edges_uniformly_separated P hsimple i j hij hij1 hji1).choose_spec.2 x hx x' hx')

/-! ### Geometry of the offset rectangles: unit normals, foot distance -/

/-- The **left normal is a unit vector** (for a nondegenerate edge). -/
lemma leftNormal_unit (hsimple : P.IsSimple) (i : ZMod P.n) : ‖P.leftNormal i‖ = 1 := by
  rw [LatticePolygon.leftNormal, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  have : ‖((-(P.edgeDir i).2, (P.edgeDir i).1) : ℝ × ℝ)‖ = ‖P.edgeDir i‖ := by
    rw [Prod.norm_def, Prod.norm_def]; simp [max_comm]
  rw [this]
  exact inv_mul_cancel₀ (by rw [norm_ne_zero_iff]; exact edgeDir_ne_zero P hsimple i)

/-- The **right normal is a unit vector**. -/
lemma rightNormal_unit (hsimple : P.IsSimple) (i : ZMod P.n) : ‖P.rightNormal i‖ = 1 := by
  rw [LatticePolygon.rightNormal, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  have : ‖(((P.edgeDir i).2, -(P.edgeDir i).1) : ℝ × ℝ)‖ = ‖P.edgeDir i‖ := by
    rw [Prod.norm_def, Prod.norm_def]; simp [max_comm]
  rw [this]
  exact inv_mul_cancel₀ (by rw [norm_ne_zero_iff]; exact edgeDir_ne_zero P hsimple i)

/-- The **foot** of the rectangle point `rectMap i nrm (s,t)`: the on-edge point
`(1-s)•vert i + s•vert(i+1)`. The rectangle point is exactly this foot plus `t • nrm`. -/
def LatticePolygon.foot (i : ZMod P.n) (s : ℝ) : ℝ × ℝ :=
  (1 - s) • toReal (P.vert i) + s • toReal (P.vert (i + 1))

/-- The foot of an interior parameter `s ∈ (0,1)` lies on edge `i`. -/
lemma foot_mem_edgeSeg (i : ZMod P.n) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    P.foot i s ∈ P.edgeSeg i := by
  rw [LatticePolygon.foot, LatticePolygon.edgeSeg]
  exact ⟨1 - s, s, by linarith [hs.2], le_of_lt hs.1, by ring, rfl⟩

/-- **Distance from a rectangle point to its foot is `|t|·‖nrm‖`.** -/
lemma dist_rectMap_foot (i : ZMod P.n) (nrm : ℝ × ℝ) (s t : ℝ) :
    dist (P.rectMap i nrm (s, t)) (P.foot i s) = |t| * ‖nrm‖ := by
  rw [LatticePolygon.rectMap, LatticePolygon.foot, dist_eq_norm,
    show (1 - s) • toReal (P.vert i) + s • toReal (P.vert (i + 1)) + t • nrm
        - ((1 - s) • toReal (P.vert i) + s • toReal (P.vert (i + 1))) = t • nrm from by abel,
    norm_smul, Real.norm_eq_abs]

/-- **A point strictly off edge `i`'s directed line is not on edge `i`.** Every point of
`edgeSeg i` lies on that line (`cross (edgeDir i) (· - vert i) = 0`). -/
lemma notMem_edgeSeg_of_cross_ne (i : ZMod P.n) {q : ℝ × ℝ}
    (hq : cross (P.edgeDir i) (q - toReal (P.vert i)) ≠ 0) : q ∉ P.edgeSeg i := by
  rw [LatticePolygon.edgeSeg, segment_eq_image]
  rintro ⟨u, _, rfl⟩
  apply hq
  simp only [LatticePolygon.edgeDir, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

/-! ### Corner-truncated offset regions (the genuinely off-boundary tube cover)

The full offset parallelograms `leftRect`/`rightRect` are *not* off-boundary near the
corners (a corner of the parallelogram can sit on an adjacent edge). We replace them by
the **corner-truncated regions**: over the open edge `s ∈ (0,1)`, the offset height `t`
is capped by `capHeight i ε s`, the minimum of `ε` and the distances from the foot
`foot i s` to every *other* edge. This makes the foot the genuinely nearest boundary
point, so the region is off-boundary by construction (`leftRegion_notMem_boundary`),
sits in `Tube ε`, and is path-connected as a region under the positive continuous graph
`capHeight` (`isPathConnected_graphRegion`). -/

/-- continuity of the foot map `s ↦ foot i s`. -/
lemma continuous_foot (i : ZMod P.n) : Continuous (P.foot i) := by
  unfold LatticePolygon.foot; fun_prop

/-- The per-edge cap term: `ε` on edge `i` itself, else the distance from the foot to
edge `j`. -/
noncomputable def LatticePolygon.capTerm (i : ZMod P.n) (ε : ℝ) (s : ℝ) (j : ZMod P.n) : ℝ :=
  if j = i then ε else Metric.infDist (P.foot i s) (P.edgeSeg j)

/-- The cap height: the finite infimum over all `j` of `capTerm`. Always `≤ ε`, and
`≤ infDist (foot i s) (edgeSeg j)` for every `j ≠ i`. -/
noncomputable def LatticePolygon.capHeight (i : ZMod P.n) (ε : ℝ) (s : ℝ) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty (α := ZMod P.n)) (P.capTerm i ε s)

lemma capHeight_le_self (i : ZMod P.n) (ε : ℝ) (s : ℝ) : P.capHeight i ε s ≤ ε := by
  have := Finset.inf'_le (P.capTerm i ε s) (Finset.mem_univ i)
  simp only [LatticePolygon.capTerm, if_true] at this
  exact this

lemma capHeight_le_edge (i : ZMod P.n) (ε : ℝ) (s : ℝ) {j : ZMod P.n} (hj : j ≠ i) :
    P.capHeight i ε s ≤ Metric.infDist (P.foot i s) (P.edgeSeg j) := by
  have := Finset.inf'_le (P.capTerm i ε s) (Finset.mem_univ j)
  simp only [LatticePolygon.capTerm, if_neg hj] at this
  exact this

lemma continuous_capHeight (i : ZMod P.n) (ε : ℝ) : Continuous (P.capHeight i ε) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hrw : P.capHeight i ε = fun s' => Finset.univ.inf' (Finset.univ_nonempty (α := ZMod P.n))
      (fun j => P.capTerm i ε s' j) := rfl
  rw [hrw]
  apply ContinuousAt.finset_inf'_apply
  intro j _
  unfold LatticePolygon.capTerm
  by_cases hj : j = i
  · simp only [if_pos hj]; exact continuousAt_const
  · simp only [if_neg hj]
    exact ((Metric.continuous_infDist_pt (P.edgeSeg j)).comp (continuous_foot P i)).continuousAt

/-- The foot of an interior parameter is distinct from the start vertex. -/
lemma foot_ne_vert (hsimple : P.IsSimple) (i : ZMod P.n) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    P.foot i s ≠ toReal (P.vert i) := by
  have hnorm : (0:ℝ) < ‖toReal (P.vert (i + 1)) - toReal (P.vert i)‖ := by
    rw [norm_pos_iff]; exact (edgeDir_ne_zero P hsimple i)
  intro h
  have hd : dist (P.foot i s) (toReal (P.vert i)) = 0 := by rw [h, dist_self]
  rw [LatticePolygon.foot] at hd
  rw [dist_eq_norm,
    show (1 - s) • toReal (P.vert i) + s • toReal (P.vert (i + 1)) - toReal (P.vert i)
        = s • (toReal (P.vert (i + 1)) - toReal (P.vert i)) from by module,
    norm_smul, Real.norm_eq_abs] at hd
  have hs0 : (0:ℝ) < |s| := by rw [abs_pos]; exact ne_of_gt hs.1
  nlinarith [hd, hs0, hnorm]

/-- The foot of an interior parameter is distinct from the end vertex. -/
lemma foot_ne_vert_succ (hsimple : P.IsSimple) (i : ZMod P.n) {s : ℝ}
    (hs : s ∈ Set.Ioo (0:ℝ) 1) : P.foot i s ≠ toReal (P.vert (i + 1)) := by
  have hnorm : (0:ℝ) < ‖toReal (P.vert (i + 1)) - toReal (P.vert i)‖ := by
    rw [norm_pos_iff]; exact (edgeDir_ne_zero P hsimple i)
  intro h
  have hd : dist (P.foot i s) (toReal (P.vert (i + 1))) = 0 := by rw [h, dist_self]
  rw [LatticePolygon.foot] at hd
  rw [dist_eq_norm,
    show (1 - s) • toReal (P.vert i) + s • toReal (P.vert (i + 1)) - toReal (P.vert (i + 1))
        = (1 - s) • (toReal (P.vert i) - toReal (P.vert (i + 1))) from by module,
    norm_smul, Real.norm_eq_abs,
    ← norm_neg (toReal (P.vert i) - toReal (P.vert (i + 1))), neg_sub] at hd
  have hs1 : (0:ℝ) < |1 - s| := by rw [abs_pos]; have := hs.2; intro hc; nlinarith
  nlinarith [hd, hs1, hnorm]

/-- **The interior foot of edge `i` lies off every other edge `j ≠ i`.** Non-adjacent
edges are disjoint from edge `i` (`IsSimple` clause 2); adjacent edges meet edge `i` only
at a shared vertex (`IsSimple` clause 3), which the interior foot avoids. -/
lemma foot_notMem_edgeSeg (hsimple : P.IsSimple) (i j : ZMod P.n) (hj : j ≠ i)
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) : P.foot i s ∉ P.edgeSeg j := by
  have hfoot : P.foot i s ∈ P.edgeSeg i := foot_mem_edgeSeg P i hs
  by_cases hadj1 : j = i + 1
  · subst hadj1
    intro hmem
    have hcap : P.foot i s ∈ P.edgeSeg i ∩ P.edgeSeg (i + 1) := ⟨hfoot, hmem⟩
    rw [hsimple.2.2 i] at hcap
    exact foot_ne_vert_succ P hsimple i hs hcap
  · by_cases hadj2 : j + 1 = i
    · intro hmem
      have hji : P.edgeSeg j ∩ P.edgeSeg (j + 1) = {toReal (P.vert (j + 1))} := hsimple.2.2 j
      have hmem2 : P.foot i s ∈ P.edgeSeg j ∩ P.edgeSeg (j + 1) := by
        rw [hadj2]; exact ⟨hmem, hfoot⟩
      rw [hji, hadj2] at hmem2
      exact foot_ne_vert P hsimple i hs hmem2
    · have hdisj : Disjoint (P.edgeSeg i) (P.edgeSeg j) :=
        hsimple.2.1 i j (Ne.symm hj) (fun h => hadj1 h.symm) hadj2
      exact fun hmem => Set.disjoint_left.mp hdisj hfoot hmem

/-- `capHeight > 0` on the open segment `s ∈ (0,1)`, for `ε > 0`: every cap term is
positive (the foot lies strictly inside edge `i`, hence off every other edge). -/
lemma capHeight_pos (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    0 < P.capHeight i ε s := by
  rw [LatticePolygon.capHeight, Finset.lt_inf'_iff]
  intro j _
  unfold LatticePolygon.capTerm
  by_cases hj : j = i
  · simp only [if_pos hj]; exact hε
  · simp only [if_neg hj]
    rw [← ((isCompact_edgeSeg P j).isClosed).notMem_iff_infDist_pos
        ⟨toReal (P.vert j), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩]
    exact foot_notMem_edgeSeg P hsimple i j hj hs

/-- **The truncated left region beside edge `i`.** The graph region over the open edge
`s ∈ (0,1)`, with offset height `t` capped by `capHeight i ε s`. -/
noncomputable def LatticePolygon.leftRegion (i : ZMod P.n) (ε : ℝ) : Set (ℝ × ℝ) :=
  P.rectMap i (P.leftNormal i) ''
    {st : ℝ × ℝ | st.1 ∈ Set.Ioo (0:ℝ) 1 ∧ 0 < st.2 ∧ st.2 < P.capHeight i ε st.1}

/-- **The truncated right region beside edge `i`.** -/
noncomputable def LatticePolygon.rightRegion (i : ZMod P.n) (ε : ℝ) : Set (ℝ × ℝ) :=
  P.rectMap i (P.rightNormal i) ''
    {st : ℝ × ℝ | st.1 ∈ Set.Ioo (0:ℝ) 1 ∧ 0 < st.2 ∧ st.2 < P.capHeight i ε st.1}

/-- **`leftRegion i ε` is path-connected** (region under the positive continuous graph
`capHeight`, via `isPathConnected_graphRegion`). -/
lemma isPathConnected_leftRegion (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (P.leftRegion i ε) := by
  apply isPathConnected_graphRegion
    ((convex_Ioo (0:ℝ) 1).isPathConnected ⟨1/2, by norm_num, by norm_num⟩)
    (continuous_capHeight P i ε) (fun s hs => capHeight_pos P hsimple i hε hs)
  exact continuous_rectMap P i (P.leftNormal i)

/-- **`rightRegion i ε` is path-connected.** -/
lemma isPathConnected_rightRegion (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (P.rightRegion i ε) := by
  apply isPathConnected_graphRegion
    ((convex_Ioo (0:ℝ) 1).isPathConnected ⟨1/2, by norm_num, by norm_num⟩)
    (continuous_capHeight P i ε) (fun s hs => capHeight_pos P hsimple i hε hs)
  exact continuous_rectMap P i (P.rightNormal i)

/-- The cross-sign of a raw `rectMap` left point is positive (perpendicular offset). -/
lemma rectMap_left_cross_pos (hsimple : P.IsSimple) (i : ZMod P.n) {s t : ℝ} (ht : 0 < t) :
    0 < cross (P.edgeDir i) (P.rectMap i (P.leftNormal i) (s, t) - toReal (P.vert i)) := by
  have hcross : cross (P.edgeDir i) (P.rectMap i (P.leftNormal i) (s, t) - toReal (P.vert i))
      = t * (‖P.edgeDir i‖⁻¹ * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2)) := by
    simp only [LatticePolygon.rectMap, LatticePolygon.leftNormal, cross, LatticePolygon.edgeDir,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul]
    ring
  rw [hcross]
  have hnorm : 0 < ‖P.edgeDir i‖⁻¹ := by
    rw [inv_pos, norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have := normSq_edgeDir_pos P hsimple i
  positivity

/-- The cross-sign of a raw `rectMap` right point is negative. -/
lemma rectMap_right_cross_neg (hsimple : P.IsSimple) (i : ZMod P.n) {s t : ℝ} (ht : 0 < t) :
    cross (P.edgeDir i) (P.rectMap i (P.rightNormal i) (s, t) - toReal (P.vert i)) < 0 := by
  have hcross : cross (P.edgeDir i) (P.rectMap i (P.rightNormal i) (s, t) - toReal (P.vert i))
      = -(t * (‖P.edgeDir i‖⁻¹ * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2))) := by
    simp only [LatticePolygon.rectMap, LatticePolygon.rightNormal, cross, LatticePolygon.edgeDir,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul]
    ring
  rw [hcross]
  have hnorm : 0 < ‖P.edgeDir i‖⁻¹ := by
    rw [inv_pos, norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have := normSq_edgeDir_pos P hsimple i
  have : 0 < t * (‖P.edgeDir i‖⁻¹ * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2)) := by positivity
  linarith

/-- **Every point of `leftRegion i ε` is off the boundary** (for `ε > 0`). Off edge `i`
by the cross-sign; off every other edge `j` since for `x' ∈ edgeSeg j`,
`dist q x' ≥ infDist (foot) (edgeSeg j) − t ≥ capHeight − t > 0`. -/
lemma leftRegion_notMem_boundary (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ}
    {q : ℝ × ℝ} (hq : q ∈ P.leftRegion i ε) : q ∉ P.boundary := by
  obtain ⟨⟨s, t⟩, ⟨hs, ht0, htcap⟩, rfl⟩ := hq
  rw [LatticePolygon.boundary, Set.mem_iUnion]
  rintro ⟨j, hmemj⟩
  by_cases hj : j = i
  · rw [hj] at hmemj
    exact notMem_edgeSeg_of_cross_ne P i (ne_of_gt (rectMap_left_cross_pos P hsimple i ht0)) hmemj
  · have hdistfoot : dist (P.rectMap i (P.leftNormal i) (s, t)) (P.foot i s) = t := by
      rw [dist_rectMap_foot, leftNormal_unit P hsimple, mul_one, abs_of_pos ht0]
    have hle : Metric.infDist (P.foot i s) (P.edgeSeg j)
        ≤ dist (P.foot i s) (P.rectMap i (P.leftNormal i) (s, t)) :=
      Metric.infDist_le_dist_of_mem hmemj
    rw [dist_comm, hdistfoot] at hle
    have hcap := capHeight_le_edge P i ε s hj
    linarith

/-- **Every point of `rightRegion i ε` is off the boundary.** -/
lemma rightRegion_notMem_boundary (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ}
    {q : ℝ × ℝ} (hq : q ∈ P.rightRegion i ε) : q ∉ P.boundary := by
  obtain ⟨⟨s, t⟩, ⟨hs, ht0, htcap⟩, rfl⟩ := hq
  rw [LatticePolygon.boundary, Set.mem_iUnion]
  rintro ⟨j, hmemj⟩
  by_cases hj : j = i
  · rw [hj] at hmemj
    exact notMem_edgeSeg_of_cross_ne P i (ne_of_lt (rectMap_right_cross_neg P hsimple i ht0)) hmemj
  · have hdistfoot : dist (P.rectMap i (P.rightNormal i) (s, t)) (P.foot i s) = t := by
      rw [dist_rectMap_foot, rightNormal_unit P hsimple, mul_one, abs_of_pos ht0]
    have hle : Metric.infDist (P.foot i s) (P.edgeSeg j)
        ≤ dist (P.foot i s) (P.rectMap i (P.rightNormal i) (s, t)) :=
      Metric.infDist_le_dist_of_mem hmemj
    rw [dist_comm, hdistfoot] at hle
    have hcap := capHeight_le_edge P i ε s hj
    linarith

/-- `leftRegion i ε ⊆ boundaryᶜ`. -/
lemma leftRegion_subset_compl_boundary (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ} :
    P.leftRegion i ε ⊆ P.boundaryᶜ :=
  fun _ hq => leftRegion_notMem_boundary P hsimple i hq

/-- `rightRegion i ε ⊆ boundaryᶜ`. -/
lemma rightRegion_subset_compl_boundary (hsimple : P.IsSimple) (i : ZMod P.n) {ε : ℝ} :
    P.rightRegion i ε ⊆ P.boundaryᶜ :=
  fun _ hq => rightRegion_notMem_boundary P hsimple i hq

/-! ### Cover-support: explicit `rectMap` coordinates (metric-agnostic)

Under the **sup-norm** of `ℝ × ℝ`, the nearest point on a segment is *not* in general the
perpendicular foot (e.g. for edge `(0,0)→(3,1)` and `q = (0,1)`, the sup-distance is `3/4`
realised along `(-1,1)`, not along the Euclidean normal `(-1,3)`). So the offset
`q − p*` from a sup-norm nearest point `p*` does **not** decompose as `t • leftNormal i`
with `t = infDist`. What *does* always hold is the purely algebraic decomposition below:
every point of the plane has unique `(edge, normal)` coordinates w.r.t. edge `i`, and the
side (left/right) is read off from `cross (edgeDir i) (q − vert i)`. This is the
metric-agnostic skeleton the corner cover is built on; the `infDist`-vs-`t` bookkeeping
is then handled separately (see the metric verdict in the module notes). -/

/-- **Explicit `rectMap` coordinates.** Any point `q` decomposes as
`q = rectMap i (leftNormal i) (s, t)` with edge coordinate
`s = ⟪q − vert i, edgeDir i⟫_E / ‖edgeDir i‖²_E` (Euclidean) and normal coordinate
`t = cross (edgeDir i) (q − vert i)·‖edgeDir i‖_sup / ‖edgeDir i‖²_E`. The product
`t·(‖d‖²_E/‖d‖_sup) = cross (edgeDir i) (q − vert i)`, so the **sign of `t` equals the
sign of the cross product**: `0 < t ↔ 0 < cross …` (strictly left) and `t < 0 ↔ cross < 0`
(strictly right). This is the metric-agnostic skeleton of the cover. -/
lemma rectMap_left_coords (hsimple : P.IsSimple) (i : ZMod P.n) (q : ℝ × ℝ) :
    ∃ s t : ℝ, q = P.rectMap i (P.leftNormal i) (s, t)
      ∧ t * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2) / ‖P.edgeDir i‖
          = cross (P.edgeDir i) (q - toReal (P.vert i)) := by
  set d := P.edgeDir i with hd
  set N : ℝ := d.1 ^ 2 + d.2 ^ 2 with hN
  have hNpos : 0 < N := normSq_edgeDir_pos P hsimple i
  have hdn : ‖d‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact edgeDir_ne_zero P hsimple i
  have hdnpos : 0 < ‖d‖ := by rw [norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  set v := toReal (P.vert i) with hv
  refine ⟨((q - v).1 * d.1 + (q - v).2 * d.2) / N,
    cross d (q - v) * ‖d‖ / N, ?_, ?_⟩
  · -- normal coefficient `(cross‖d‖/N)·‖d‖⁻¹ = cross/N`
    rw [LatticePolygon.rectMap, LatticePolygon.leftNormal, ← hd]
    rw [show (cross d (q - v) * ‖d‖ / N) • (‖d‖⁻¹ • (-d.2, d.1))
        = (cross d (q - v) / N) • ((-d.2, d.1) : ℝ × ℝ) from by
      rw [smul_smul]; congr 1; field_simp]
    have hs : (1 - ((q - v).1 * d.1 + (q - v).2 * d.2) / N) • v
        + (((q - v).1 * d.1 + (q - v).2 * d.2) / N) • toReal (P.vert (i + 1))
        = v + (((q - v).1 * d.1 + (q - v).2 * d.2) / N) • d := by
      rw [hd, LatticePolygon.edgeDir, ← hv]; module
    rw [hs]
    -- componentwise: v + s•d + (cross/N)•(-d.2,d.1) = q
    have hNz : N ≠ 0 := ne_of_gt hNpos
    have key1 : ((q - v).1 * d.1 + (q - v).2 * d.2) / N * d.1
        + cross d (q - v) / N * (-d.2) = (q - v).1 := by
      rw [cross]; field_simp [hN]; ring
    have key2 : ((q - v).1 * d.1 + (q - v).2 * d.2) / N * d.2
        + cross d (q - v) / N * d.1 = (q - v).2 := by
      rw [cross]; field_simp [hN]; ring
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul,
        Prod.fst_sub, Prod.snd_sub, hv] at key1 ⊢
      linarith [key1]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        Prod.fst_sub, Prod.snd_sub, hv] at key2 ⊢
      linarith [key2]
  · field_simp

/-- **Left-side membership from the cross-sign.** A point `q` strictly to the left of edge
`i`'s line (`0 < cross (edgeDir i) (q − vert i)`) whose edge coordinate `s` lies in `(0,1)`
sits in `leftRect i ε` for every `ε` above its normal coordinate `t > 0`. The witness
`(s,t)` comes from `rectMap_left_coords`; positivity of `t` follows from the cross-sign
since `t·(‖d‖²_E/‖d‖_sup) = cross > 0` with `‖d‖²_E/‖d‖_sup > 0`. -/
lemma exists_mem_leftRect_of_cross_pos (hsimple : P.IsSimple) (i : ZMod P.n) {q : ℝ × ℝ}
    (hcross : 0 < cross (P.edgeDir i) (q - toReal (P.vert i)))
    {s : ℝ} (_hs : s ∈ Set.Ioo (0:ℝ) 1)
    (hsval : s = ((q - toReal (P.vert i)).1 * (P.edgeDir i).1
        + (q - toReal (P.vert i)).2 * (P.edgeDir i).2)
        / ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2)) :
    ∃ t : ℝ, 0 < t ∧ q = P.rectMap i (P.leftNormal i) (s, t) := by
  obtain ⟨s', t, hq, ht⟩ := rectMap_left_coords P hsimple i q
  -- s' is forced to equal s (same formula); extract t > 0
  have hNpos : 0 < (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 := normSq_edgeDir_pos P hsimple i
  have hdnpos : 0 < ‖P.edgeDir i‖ := by rw [norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have htpos : 0 < t := by
    by_contra h; push Not at h
    have : t * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2) / ‖P.edgeDir i‖ ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hdnpos.le
      exact mul_nonpos_of_nonpos_of_nonneg h hNpos.le
    rw [ht] at this; linarith
  refine ⟨t, htpos, ?_⟩
  rw [hq]; congr 2
  -- s' = s by the same coordinate formula
  rw [hsval]
  have : s' = ((q - toReal (P.vert i)).1 * (P.edgeDir i).1
      + (q - toReal (P.vert i)).2 * (P.edgeDir i).2)
      / ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2) := by
    -- recover s' from rectMap by cross with the normal `(-d.2,d.1)`'s perpendicular
    -- direction: take the edge-direction inner product
    have hqeq := hq
    rw [LatticePolygon.rectMap, LatticePolygon.leftNormal] at hqeq
    have hd1 : (q - toReal (P.vert i)).1
        = s' * (P.edgeDir i).1 + (t * ‖P.edgeDir i‖⁻¹) * (-(P.edgeDir i).2) := by
      have := congrArg Prod.fst hqeq
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul,
        Prod.fst_sub, LatticePolygon.edgeDir] at this ⊢
      linear_combination this
    have hd2 : (q - toReal (P.vert i)).2
        = s' * (P.edgeDir i).2 + (t * ‖P.edgeDir i‖⁻¹) * (P.edgeDir i).1 := by
      have := congrArg Prod.snd hqeq
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        Prod.snd_sub, LatticePolygon.edgeDir] at this ⊢
      linear_combination this
    rw [hd1, hd2]
    field_simp
    ring
  rw [this]

/-- `rectMap i (rightNormal i) (s, t) = rectMap i (leftNormal i) (s, -t)` since
`rightNormal i = -leftNormal i`. -/
lemma rectMap_rightNormal_eq (i : ZMod P.n) (s t : ℝ) :
    P.rectMap i (P.rightNormal i) (s, t) = P.rectMap i (P.leftNormal i) (s, -t) := by
  simp only [LatticePolygon.rectMap, LatticePolygon.rightNormal, LatticePolygon.leftNormal]
  rw [show (((P.edgeDir i).2, -(P.edgeDir i).1) : ℝ × ℝ)
      = -(-(P.edgeDir i).2, (P.edgeDir i).1) from by simp]
  module

/-- **Right-side membership from the cross-sign.** Mirror of `exists_mem_leftRect_of_cross_pos`:
a point strictly to the right (`cross (edgeDir i) (q − vert i) < 0`) with edge coordinate
`s ∈ (0,1)` sits in `rightRect i ε` for `ε` above its normal coordinate. The left coordinate
`t_L < 0` flips to the positive right coordinate `t = -t_L` via `rectMap_rightNormal_eq`. -/
lemma exists_mem_rightRect_of_cross_neg (hsimple : P.IsSimple) (i : ZMod P.n) {q : ℝ × ℝ}
    (hcross : cross (P.edgeDir i) (q - toReal (P.vert i)) < 0)
    {s : ℝ} (hsval : s = ((q - toReal (P.vert i)).1 * (P.edgeDir i).1
        + (q - toReal (P.vert i)).2 * (P.edgeDir i).2)
        / ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2)) :
    ∃ t : ℝ, 0 < t ∧ q = P.rectMap i (P.rightNormal i) (s, t) := by
  obtain ⟨s', tL, hq, ht⟩ := rectMap_left_coords P hsimple i q
  have hNpos : 0 < (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 := normSq_edgeDir_pos P hsimple i
  have hdnpos : 0 < ‖P.edgeDir i‖ := by rw [norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  -- tL < 0 since tL·(N/‖d‖) = cross < 0
  have htneg : tL < 0 := by
    by_contra h; push Not at h
    have : 0 ≤ tL * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2) / ‖P.edgeDir i‖ := by positivity
    rw [ht] at this; linarith
  -- s' = s (same coordinate formula, recovered as in the left lemma)
  have hss : s' = s := by
    rw [hsval]
    rw [LatticePolygon.rectMap, LatticePolygon.leftNormal] at hq
    have hd1 : (q - toReal (P.vert i)).1
        = s' * (P.edgeDir i).1 + (tL * ‖P.edgeDir i‖⁻¹) * (-(P.edgeDir i).2) := by
      have := congrArg Prod.fst hq
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul,
        Prod.fst_sub, LatticePolygon.edgeDir] at this ⊢
      linear_combination this
    have hd2 : (q - toReal (P.vert i)).2
        = s' * (P.edgeDir i).2 + (tL * ‖P.edgeDir i‖⁻¹) * (P.edgeDir i).1 := by
      have := congrArg Prod.snd hq
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        Prod.snd_sub, LatticePolygon.edgeDir] at this ⊢
      linear_combination this
    rw [hd1, hd2]; field_simp; ring
  refine ⟨-tL, by linarith, ?_⟩
  rw [rectMap_rightNormal_eq, neg_neg, ← hss, hq]

/-! ### Corner caps: the path-connected wedge filling the gap between the two
truncated edge-regions at a convex *or reflex* vertex.

At the shared vertex `v = vert (i+1)` of edges `i` and `i+1`, the two truncated regions
`leftRegion i` and `leftRegion (i+1)` leave a small wedge near `v` uncovered (the regions
are capped away from the endpoints). The **left cap** fills it: `{v + t•u : u ∈ dirArc, 0 < t < capR}`
where `dirArc` is the (convex, nonempty) cone of unit-bounded directions strictly left of
**both** incident edges, and `capR < min featureSize edgeClearance` is small enough that the
cap meets only the two incident edges (killed by the cross-sign). -/

/-- The **left direction-arc** at vertex `i+1`: unit-bounded directions strictly to the
left of both incident edges. Convex (intersection of two half-planes and the unit ball)
and nonempty (`exists_dir_left_of_both`). -/
def LatticePolygon.leftDirArc (i : ZMod P.n) : Set (ℝ × ℝ) :=
  {u : ℝ × ℝ | 0 < cross (P.edgeDir i) u ∧ 0 < cross (P.edgeDir (i + 1)) u ∧ ‖u‖ < 1}

/-- The **right direction-arc** at vertex `i+1`. -/
def LatticePolygon.rightDirArc (i : ZMod P.n) : Set (ℝ × ℝ) :=
  {u : ℝ × ℝ | cross (P.edgeDir i) u < 0 ∧ cross (P.edgeDir (i + 1)) u < 0 ∧ ‖u‖ < 1}

lemma convex_unitBall : Convex ℝ {u : ℝ × ℝ | ‖u‖ < 1} := by
  have : {u : ℝ × ℝ | ‖u‖ < 1} = Metric.ball (0 : ℝ × ℝ) 1 := by
    ext u; simp [Metric.mem_ball, dist_zero_right]
  rw [this]; exact convex_ball 0 1

lemma convex_leftDirArc (i : ZMod P.n) : Convex ℝ (P.leftDirArc i) := by
  have h1 : Convex ℝ {u : ℝ × ℝ | 0 < cross (P.edgeDir i) u} := by
    simpa using convex_halfSpace_gt (isLinearMap_cross (P.edgeDir i)) 0
  have h2 : Convex ℝ {u : ℝ × ℝ | 0 < cross (P.edgeDir (i + 1)) u} := by
    simpa using convex_halfSpace_gt (isLinearMap_cross (P.edgeDir (i + 1))) 0
  have hset : P.leftDirArc i
      = {u | 0 < cross (P.edgeDir i) u} ∩ {u | 0 < cross (P.edgeDir (i + 1)) u}
        ∩ {u | ‖u‖ < 1} := by
    ext u; simp only [LatticePolygon.leftDirArc, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
  rw [hset]; exact (h1.inter h2).inter convex_unitBall

lemma convex_rightDirArc (i : ZMod P.n) : Convex ℝ (P.rightDirArc i) := by
  have h1 : Convex ℝ {u : ℝ × ℝ | cross (P.edgeDir i) u < 0} := by
    simpa using convex_halfSpace_lt (isLinearMap_cross (P.edgeDir i)) 0
  have h2 : Convex ℝ {u : ℝ × ℝ | cross (P.edgeDir (i + 1)) u < 0} := by
    simpa using convex_halfSpace_lt (isLinearMap_cross (P.edgeDir (i + 1))) 0
  have hset : P.rightDirArc i
      = {u | cross (P.edgeDir i) u < 0} ∩ {u | cross (P.edgeDir (i + 1)) u < 0}
        ∩ {u | ‖u‖ < 1} := by
    ext u; simp only [LatticePolygon.rightDirArc, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
  rw [hset]; exact (h1.inter h2).inter convex_unitBall

/-- The left direction-arc is nonempty: scale the cone witness to norm `< 1`. -/
lemma leftDirArc_nonempty (hsimple : P.IsSimple) (i : ZMod P.n) :
    (P.leftDirArc i).Nonempty := by
  obtain ⟨u, hu1, hu2⟩ := exists_dir_left_of_both P hsimple i
  have hune : u ≠ 0 := by
    rintro rfl; simp only [cross, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero] at hu1; linarith
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hune
  set c : ℝ := 1 / (2 * ‖u‖) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨c • u, ?_, ?_, ?_⟩
  · rw [(isLinearMap_cross (P.edgeDir i)).map_smul]; positivity
  · rw [(isLinearMap_cross (P.edgeDir (i + 1))).map_smul]; positivity
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc]
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith

/-- The right direction-arc is nonempty. -/
lemma rightDirArc_nonempty (hsimple : P.IsSimple) (i : ZMod P.n) :
    (P.rightDirArc i).Nonempty := by
  obtain ⟨u, hu1, hu2⟩ := exists_dir_right_of_both P hsimple i
  have hune : u ≠ 0 := by
    rintro rfl; simp only [cross, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero] at hu1; linarith
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hune
  set c : ℝ := 1 / (2 * ‖u‖) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨c • u, ?_, ?_, ?_⟩
  · rw [(isLinearMap_cross (P.edgeDir i)).map_smul]
    exact mul_neg_of_pos_of_neg hcpos hu1
  · rw [(isLinearMap_cross (P.edgeDir (i + 1))).map_smul]
    exact mul_neg_of_pos_of_neg hcpos hu2
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc]
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith

/-- The **cap map** at vertex `i+1`: `(u,t) ↦ vert(i+1) + t•u`. -/
def LatticePolygon.capMap (i : ZMod P.n) : (ℝ × ℝ) × ℝ → ℝ × ℝ :=
  fun ut => toReal (P.vert (i + 1)) + ut.2 • ut.1

lemma continuous_capMap (i : ZMod P.n) : Continuous (P.capMap i) := by
  unfold LatticePolygon.capMap; fun_prop

/-- The **left corner cap** at vertex `i+1`: the wedge `{vert(i+1) + t•u : u ∈ leftDirArc, 0 < t < capR}`. -/
def LatticePolygon.leftCap (i : ZMod P.n) (capR : ℝ) : Set (ℝ × ℝ) :=
  P.capMap i '' {ut : (ℝ × ℝ) × ℝ | ut.1 ∈ P.leftDirArc i ∧ 0 < ut.2 ∧ ut.2 < capR}

/-- The **right corner cap** at vertex `i+1`. -/
def LatticePolygon.rightCap (i : ZMod P.n) (capR : ℝ) : Set (ℝ × ℝ) :=
  P.capMap i '' {ut : (ℝ × ℝ) × ℝ | ut.1 ∈ P.rightDirArc i ∧ 0 < ut.2 ∧ ut.2 < capR}

/-! ### The norm bridge: sup-norm (`dist`) vs Euclidean (`eDist`)

`ℝ × ℝ` carries the **sup-norm** `‖v‖ = max |v.1| |v.2|`, which is what `dist`, `infDist`,
and `Tube` use. The offset rectangles' perpendicular geometry, however, is genuinely
*Euclidean*: `q - foot i s = t • leftNormal i` and the Euclidean length `eDist (leftNormal i)`
is `‖edgeDir i‖_E / ‖edgeDir i‖_sup`, **not** `1`. We record the two-sided equivalence
`‖v‖ ≤ eDist v ≤ √2 · ‖v‖` to convert the sup-distance bound from `Tube` into a Euclidean
perpendicular-offset bound for the cover, and back. -/

/-- The Euclidean norm of `v : ℝ × ℝ` (the geometry is Euclidean even though `dist` is sup). -/
noncomputable def eDist (v : ℝ × ℝ) : ℝ := Real.sqrt (v.1 ^ 2 + v.2 ^ 2)

lemma eDist_nonneg (v : ℝ × ℝ) : 0 ≤ eDist v := Real.sqrt_nonneg _

/-- **Lower bridge**: the sup-norm is `≤` the Euclidean norm. -/
lemma norm_le_eDist (v : ℝ × ℝ) : ‖v‖ ≤ eDist v := by
  rw [eDist, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    show max |v.1| |v.2| = Real.sqrt (max |v.1| |v.2| ^ 2) from
      (Real.sqrt_sq (le_max_of_le_left (abs_nonneg _))).symm]
  apply Real.sqrt_le_sqrt
  rcases le_total |v.1| |v.2| with h | h <;> [rw [max_eq_right h]; rw [max_eq_left h]] <;>
    nlinarith [sq_abs v.1, sq_abs v.2, sq_nonneg v.1, sq_nonneg v.2]

/-- **Upper bridge**: the Euclidean norm is `≤ √2 ·` the sup-norm. -/
lemma eDist_le_sqrt2_norm (v : ℝ × ℝ) : eDist v ≤ Real.sqrt 2 * ‖v‖ := by
  rw [eDist, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    show Real.sqrt 2 * max |v.1| |v.2| = Real.sqrt 2 * Real.sqrt (max |v.1| |v.2| ^ 2) from by
      rw [Real.sqrt_sq (le_max_of_le_left (abs_nonneg _))],
    ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  rcases le_total |v.1| |v.2| with h | h
  · rw [max_eq_right h]; nlinarith [sq_abs v.1, sq_abs v.2, mul_self_le_mul_self (abs_nonneg v.1) h]
  · rw [max_eq_left h]; nlinarith [sq_abs v.1, sq_abs v.2, mul_self_le_mul_self (abs_nonneg v.2) h]

/-- `eDist` is absolutely homogeneous. -/
lemma eDist_smul (t : ℝ) (v : ℝ × ℝ) : eDist (t • v) = |t| * eDist v := by
  rw [eDist, eDist, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul,
    show (t * v.1) ^ 2 + (t * v.2) ^ 2 = t ^ 2 * (v.1 ^ 2 + v.2 ^ 2) from by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- `eDist (v - w)` is the Euclidean distance, dominated by `√2 ·` the sup-distance. -/
lemma eDist_sub_le_sqrt2_dist (v w : ℝ × ℝ) : eDist (v - w) ≤ Real.sqrt 2 * dist v w := by
  rw [dist_eq_norm]; exact eDist_le_sqrt2_norm _

/-- **The Euclidean length of the left normal** is `‖edgeDir i‖_E / ‖edgeDir i‖_sup`, where
`‖edgeDir i‖_E = √(d.1²+d.2²) = eDist (edgeDir i)`. In particular it is positive but, unlike
the sup-norm, generally `≠ 1`. -/
lemma eDist_leftNormal (_ : P.IsSimple) (i : ZMod P.n) :
    eDist (P.leftNormal i) = ‖P.edgeDir i‖⁻¹ * eDist (P.edgeDir i) := by
  rw [LatticePolygon.leftNormal, eDist_smul, abs_of_nonneg (by positivity)]
  congr 1
  rw [eDist, eDist]; congr 1; ring

lemma eDist_rightNormal (_ : P.IsSimple) (i : ZMod P.n) :
    eDist (P.rightNormal i) = ‖P.edgeDir i‖⁻¹ * eDist (P.edgeDir i) := by
  rw [LatticePolygon.rightNormal, eDist_smul, abs_of_nonneg (by positivity)]
  congr 1
  rw [eDist, eDist]; congr 1; ring

/-! ### Clean cone characterisation of cap membership

A point `q` lies in `leftCap i capR` exactly when its offset `w = q − vert(i+1)` is in the
open left cone of both incident edges and has sup-norm `< capR`. (The scale `t` and unit
direction `u = w/t` are recovered by normalising.) This is the convenient membership form for
the cover, where we only know cross-signs and a metric ball around the corner. -/

/-! ### The perpendicular-foot inequality (Euclidean)

For `q = rectMap i (leftNormal i) (sE, t)`, the offset `q − foot i sE = t • leftNormal i` is
Euclidean-perpendicular to the edge direction, so `foot i sE` is the Euclidean-nearest point
of the edge *line* to `q`. Hence `eDist (q − foot i sE) ≤ eDist (q − foot i s')` for every
`s'` (in particular for the sup-nearest boundary point). Pythagoras: the two offsets are
orthogonal, so the squared distance only grows when we move the foot along the edge. -/

/-- **Perpendicular-foot inequality (left).** The Euclidean distance to the perpendicular
foot `foot i sE` is `≤` the Euclidean distance to any other on-line point `foot i s'`. -/
lemma eDist_perp_foot_le_left (i : ZMod P.n) {sE t s' : ℝ} {q : ℝ × ℝ}
    (hq : q = P.rectMap i (P.leftNormal i) (sE, t)) :
    eDist (q - P.foot i sE) ≤ eDist (q - P.foot i s') := by
  have hperp : q - P.foot i sE = t • P.leftNormal i := by
    rw [hq, LatticePolygon.rectMap, LatticePolygon.foot]; abel
  have hsplit : q - P.foot i s' = t • P.leftNormal i + (sE - s') • P.edgeDir i := by
    rw [hq, LatticePolygon.rectMap, LatticePolygon.foot, LatticePolygon.edgeDir]; module
  have horth : (P.leftNormal i).1 * (P.edgeDir i).1 + (P.leftNormal i).2 * (P.edgeDir i).2 = 0 := by
    simp only [LatticePolygon.leftNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [eDist, eDist, hperp, hsplit]
  apply Real.sqrt_le_sqrt
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [sq_nonneg ((sE - s') * (P.edgeDir i).1), sq_nonneg ((sE - s') * (P.edgeDir i).2),
    mul_eq_zero_of_right (2 * t * (sE - s')) horth]

/-- **Perpendicular-foot inequality (right).** -/
lemma eDist_perp_foot_le_right (i : ZMod P.n) {sE t s' : ℝ} {q : ℝ × ℝ}
    (hq : q = P.rectMap i (P.rightNormal i) (sE, t)) :
    eDist (q - P.foot i sE) ≤ eDist (q - P.foot i s') := by
  have hperp : q - P.foot i sE = t • P.rightNormal i := by
    rw [hq, LatticePolygon.rectMap, LatticePolygon.foot]; abel
  have hsplit : q - P.foot i s' = t • P.rightNormal i + (sE - s') • P.edgeDir i := by
    rw [hq, LatticePolygon.rectMap, LatticePolygon.foot, LatticePolygon.edgeDir]; module
  have horth : (P.rightNormal i).1 * (P.edgeDir i).1 + (P.rightNormal i).2 * (P.edgeDir i).2 = 0 := by
    simp only [LatticePolygon.rightNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [eDist, eDist, hperp, hsplit]
  apply Real.sqrt_le_sqrt
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [sq_nonneg ((sE - s') * (P.edgeDir i).1), sq_nonneg ((sE - s') * (P.edgeDir i).2),
    mul_eq_zero_of_right (2 * t * (sE - s')) horth]

/-- **The sup-distance to the perpendicular foot is the normal coordinate.** For
`q = rectMap i (leftNormal i) (sE, t)` with `t ≥ 0`, `dist q (foot i sE) = t` (the left
normal is sup-unit). -/
lemma dist_foot_eq_coord_left (hsimple : P.IsSimple) (i : ZMod P.n) {sE t : ℝ} (ht : 0 ≤ t)
    {q : ℝ × ℝ} (hq : q = P.rectMap i (P.leftNormal i) (sE, t)) :
    dist q (P.foot i sE) = t := by
  rw [hq, dist_rectMap_foot, leftNormal_unit P hsimple, mul_one, abs_of_nonneg ht]

lemma dist_foot_eq_coord_right (hsimple : P.IsSimple) (i : ZMod P.n) {sE t : ℝ} (ht : 0 ≤ t)
    {q : ℝ × ℝ} (hq : q = P.rectMap i (P.rightNormal i) (sE, t)) :
    dist q (P.foot i sE) = t := by
  rw [hq, dist_rectMap_foot, rightNormal_unit P hsimple, mul_one, abs_of_nonneg ht]

/-- **The normal coordinate is `≤ √2 ·` the distance to any on-edge point** (left). The
sup-distance to the perpendicular foot equals the normal coordinate `t`, dominated by the
Euclidean distance, which (perpendicular foot) is `≤` the Euclidean distance to any other
on-edge point and hence `≤ √2 ·` the sup-distance. -/
lemma coord_le_sqrt2_dist_left (hsimple : P.IsSimple) (i : ZMod P.n) {sE t s' : ℝ} (ht : 0 ≤ t)
    {q : ℝ × ℝ} (hq : q = P.rectMap i (P.leftNormal i) (sE, t)) :
    t ≤ Real.sqrt 2 * dist q (P.foot i s') := by
  rw [(dist_foot_eq_coord_left P hsimple i ht hq).symm, dist_eq_norm]
  calc ‖q - P.foot i sE‖ ≤ eDist (q - P.foot i sE) := norm_le_eDist _
    _ ≤ eDist (q - P.foot i s') := eDist_perp_foot_le_left P i hq
    _ ≤ Real.sqrt 2 * dist q (P.foot i s') := eDist_sub_le_sqrt2_dist _ _

/-- **The normal coordinate is `≤ √2 ·` the distance to any on-edge point** (right). -/
lemma coord_le_sqrt2_dist_right (hsimple : P.IsSimple) (i : ZMod P.n) {sE t s' : ℝ} (ht : 0 ≤ t)
    {q : ℝ × ℝ} (hq : q = P.rectMap i (P.rightNormal i) (sE, t)) :
    t ≤ Real.sqrt 2 * dist q (P.foot i s') := by
  rw [(dist_foot_eq_coord_right P hsimple i ht hq).symm, dist_eq_norm]
  calc ‖q - P.foot i sE‖ ≤ eDist (q - P.foot i sE) := norm_le_eDist _
    _ ≤ eDist (q - P.foot i s') := eDist_perp_foot_le_right P i hq
    _ ≤ Real.sqrt 2 * dist q (P.foot i s') := eDist_sub_le_sqrt2_dist _ _


/-! ### Angle-parametrized direction caps (reflex-safe)

The old `leftDirArc`/`rightDirArc` caps were the cone "strictly left of **both** edges"
(resp. right). At a *reflex* vertex these cover only the convex side — a point that is
left of one incident edge and right of the other near the vertex is in *neither* cap, so
the cover failed. The fix parametrizes directions by **angle**: the two boundary rays
`−edgeDir i` (incoming reversed) and `edgeDir (i+1)` (outgoing) cut the punctured plane
into two angular sectors, each of which is a genuine `θ`-interval (so it works for
reflex sectors `> π`). -/

/-- The unit direction at angle `θ`: `(cos θ, sin θ)`. -/
noncomputable def dirOf (θ : ℝ) : ℝ × ℝ := (Real.cos θ, Real.sin θ)

lemma continuous_dirOf : Continuous dirOf := by unfold dirOf; fun_prop

/-- The angle (argument) of a nonzero direction `d : ℝ × ℝ`, via `Complex.arg`. -/
noncomputable def argOf (d : ℝ × ℝ) : ℝ := (Complex.mk d.1 d.2).arg

/-- **Direction surjection.** For `d ≠ 0`, `dirOf (argOf d)` is the positive Euclidean
normalization `(eDist d)⁻¹ • d` of `d` — a *positive* multiple pointing the same way. -/
lemma dirOf_argOf {d : ℝ × ℝ} (h : d ≠ 0) : dirOf (argOf d) = (eDist d)⁻¹ • d := by
  have hz : (Complex.mk d.1 d.2) ≠ 0 := by
    simp only [ne_eq, Complex.ext_iff, Complex.zero_re, Complex.zero_im, not_and]
    intro h1 h2; exact h (Prod.ext h1 h2)
  have hnorm : ‖(Complex.mk d.1 d.2)‖ = eDist d := by
    rw [Complex.norm_def, Complex.normSq_mk, eDist]; congr 1; ring
  unfold dirOf argOf
  rw [Complex.cos_arg hz, Complex.sin_arg (Complex.mk d.1 d.2), hnorm]
  ext <;> simp [Prod.smul_fst, Prod.smul_snd, div_eq_inv_mul]

/-- `dirOf θ` is Euclidean-unit. -/
lemma eDist_dirOf (θ : ℝ) : eDist (dirOf θ) = 1 := by
  simp only [eDist, dirOf]
  rw [← Real.sqrt_one]; congr 1; nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `dirOf θ ≠ 0`. -/
lemma dirOf_ne_zero (θ : ℝ) : dirOf θ ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
  simp only [dirOf, Prod.fst_zero, Prod.snd_zero] at h1 h2
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **Scaling by a positive constant preserves `argOf`.** -/
lemma argOf_smul_pos {r : ℝ} (hr : 0 < r) (w : ℝ × ℝ) : argOf (r • w) = argOf w := by
  simp only [argOf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show Complex.mk (r * w.1) (r * w.2) = (r : ℂ) * Complex.mk w.1 w.2 from by
      apply Complex.ext <;> simp, Complex.arg_real_mul _ hr]

/-- **`argOf (dirOf θ)` represents `θ` mod 2π.** -/
lemma argOf_dirOf_angle_eq (θ : ℝ) : (↑(argOf (dirOf θ)) : Real.Angle) = ↑θ := by
  have h1 : dirOf (argOf (dirOf θ)) = dirOf θ := by
    rw [dirOf_argOf (dirOf_ne_zero θ), eDist_dirOf, inv_one, one_smul]
  exact Real.Angle.cos_sin_inj (congrArg Prod.fst h1) (congrArg Prod.snd h1)

/-- **The angle of a positive multiple of `dirOf θ` represents `θ` mod 2π.** -/
lemma argOf_smul_dirOf_angle_eq {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (↑(argOf (r • dirOf θ)) : Real.Angle) = ↑θ := by
  rw [argOf_smul_pos hr, argOf_dirOf_angle_eq]

/-- **The sector map** at vertex `i+1`: `(θ,r) ↦ vert(i+1) + r • dirOf θ`. -/
noncomputable def LatticePolygon.sectorMap (i : ZMod P.n) : ℝ × ℝ → ℝ × ℝ :=
  fun θr => toReal (P.vert (i + 1)) + θr.2 • dirOf θr.1

lemma continuous_sectorMap (i : ZMod P.n) : Continuous (P.sectorMap i) := by
  unfold LatticePolygon.sectorMap
  exact continuous_const.add ((continuous_snd).smul (continuous_dirOf.comp continuous_fst))

/-- An **angular sector cap** at vertex `i+1`: the set
`{vert(i+1) + r • dirOf θ : θ ∈ Ioo lo hi, 0 < r < capR}`, the image of the convex box
`Ioo lo hi ×ˢ Ioo 0 capR` under the sector map. The angle interval `(lo, hi)` is one of the
two sectors between the boundary rays. Reflex-safe: any width up to `2π` is allowed. -/
noncomputable def LatticePolygon.sectorCap (i : ZMod P.n) (lo hi capR : ℝ) : Set (ℝ × ℝ) :=
  P.sectorMap i '' (Set.Ioo lo hi ×ˢ Set.Ioo (0:ℝ) capR)

/-- **A sector cap is path-connected** (continuous image of a convex nonempty box). -/
lemma isPathConnected_sectorCap (i : ZMod P.n) {lo hi capR : ℝ}
    (hlh : lo < hi) (hR : 0 < capR) : IsPathConnected (P.sectorCap i lo hi capR) := by
  apply IsPathConnected.image _ (continuous_sectorMap P i)
  apply Convex.isPathConnected ((convex_Ioo lo hi).prod (convex_Ioo 0 capR))
  exact ⟨((lo + hi) / 2, capR / 2), ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩

/-- The sup-norm of a unit direction is `≤ 1` (`|cos|, |sin| ≤ 1`). -/
lemma norm_dirOf_le (θ : ℝ) : ‖dirOf θ‖ ≤ 1 := by
  rw [dirOf, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
  exact ⟨Real.abs_cos_le_one θ, Real.abs_sin_le_one θ⟩

/-- **Every point of a sector cap is off the boundary** (for `capR ≤ featureSize`), provided
each interior angle `θ ∈ (lo, hi)` makes `dirOf θ` non-parallel to *both* incident edges
(`cross (edgeDir ·) (dirOf θ) ≠ 0`). Off the two incident edges by the nonzero cross-sign
(strictly between the two boundary rays); off every non-incident edge by `featureSize_le`,
since the cap point is within `capR ≤ featureSize` of the shared vertex `vert(i+1)`. -/
lemma sectorCap_subset_compl_boundary (i : ZMod P.n) {lo hi capR : ℝ}
    (hRfs : capR ≤ P.featureSize)
    (hcrL : ∀ θ ∈ Set.Ioo lo hi, cross (P.edgeDir i) (dirOf θ) ≠ 0)
    (hcrR : ∀ θ ∈ Set.Ioo lo hi, cross (P.edgeDir (i + 1)) (dirOf θ) ≠ 0) :
    P.sectorCap i lo hi capR ⊆ P.boundaryᶜ := by
  intro q hq
  obtain ⟨⟨θ, r⟩, ⟨hθ, hr0, hrR⟩, rfl⟩ := hq
  rw [Set.mem_compl_iff, LatticePolygon.boundary, Set.mem_iUnion]
  rintro ⟨j, hmemj⟩
  simp only [LatticePolygon.sectorMap] at hmemj ⊢
  by_cases hji : j = i
  · subst hji
    apply notMem_edgeSeg_of_cross_ne P j _ hmemj
    have hexp : toReal (P.vert (j + 1)) + r • dirOf θ - toReal (P.vert j)
        = P.edgeDir j + r • dirOf θ := by rw [LatticePolygon.edgeDir]; abel
    rw [hexp]
    have heq : cross (P.edgeDir j) (P.edgeDir j + r • dirOf θ)
        = r * cross (P.edgeDir j) (dirOf θ) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [heq]; exact mul_ne_zero (ne_of_gt hr0) (hcrL θ hθ)
  · by_cases hji1 : j = i + 1
    · subst hji1
      apply notMem_edgeSeg_of_cross_ne P (i + 1) _ hmemj
      have hexp : toReal (P.vert (i + 1)) + r • dirOf θ - toReal (P.vert (i + 1))
          = r • dirOf θ := by abel
      rw [hexp]
      have heq : cross (P.edgeDir (i + 1)) (r • dirOf θ)
          = r * cross (P.edgeDir (i + 1)) (dirOf θ) := by
        simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [heq]; exact mul_ne_zero (ne_of_gt hr0) (hcrR θ hθ)
    · have hfs : P.featureSize ≤ Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j) :=
        featureSize_le P (i + 1) j hji1 (by rw [add_sub_cancel_right]; exact hji)
      have hle : Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j)
          ≤ dist (toReal (P.vert (i + 1))) (toReal (P.vert (i + 1)) + r • dirOf θ) :=
        Metric.infDist_le_dist_of_mem hmemj
      rw [dist_eq_norm, show toReal (P.vert (i + 1)) - (toReal (P.vert (i + 1)) + r • dirOf θ)
          = -(r • dirOf θ) from by abel, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr0] at hle
      have hd1 : r * ‖dirOf θ‖ ≤ r * 1 :=
        mul_le_mul_of_nonneg_left (norm_dirOf_le θ) (le_of_lt hr0)
      rw [mul_one] at hd1
      linarith

/-! ### Ray-based off-boundary criterion (handles the collinear-interior directions)

The cross-sign criterion above excludes the entire *line* of each incident edge, but only
the two **rays** `−edgeDir i` (edge `i` emanating from `v=vert(i+1)`) and `+edgeDir(i+1)`
(edge `i+1` from `v`) are actually on the boundary. The opposite ray directions `+edgeDir i`
and `−edgeDir(i+1)` lie *interior* to the sectors and are off the boundary even though their
cross with the respective edge vanishes. The genuinely reflex-safe criterion therefore keys
on "the offset is **not a nonnegative multiple** of the boundary-ray direction". -/

/-- A point `v + w` (with `v = vert(i+1)`) is **off edge `i+1`** when `w` is not a nonnegative
multiple of the outgoing ray direction `edgeDir(i+1)`. -/
lemma notMem_edgeSeg_succ_of_not_ray (i : ZMod P.n) {w : ℝ × ℝ}
    (hne : ∀ s : ℝ, 0 ≤ s → w ≠ s • P.edgeDir (i + 1)) :
    toReal (P.vert (i + 1)) + w ∉ P.edgeSeg (i + 1) := by
  rw [LatticePolygon.edgeSeg, segment_eq_image]
  rintro ⟨s, ⟨hs0, _⟩, heq⟩
  apply hne s hs0
  have : toReal (P.vert (i + 1)) + w = toReal (P.vert (i + 1)) + s • P.edgeDir (i + 1) := by
    rw [← heq, LatticePolygon.edgeDir]; module
  exact add_left_cancel this

/-- A point `v + w` (with `v = vert(i+1)`) is **off edge `i`** when `w` is not a nonnegative
multiple of the incoming ray direction `−edgeDir i`. -/
lemma notMem_edgeSeg_self_of_not_ray (i : ZMod P.n) {w : ℝ × ℝ}
    (hne : ∀ s : ℝ, 0 ≤ s → w ≠ s • (-(P.edgeDir i))) :
    toReal (P.vert (i + 1)) + w ∉ P.edgeSeg i := by
  rw [LatticePolygon.edgeSeg, segment_eq_image]
  rintro ⟨s, ⟨_, hs1⟩, heq⟩
  apply hne (1 - s) (by linarith)
  have : toReal (P.vert (i + 1)) + w = toReal (P.vert (i + 1)) + (1 - s) • (-(P.edgeDir i)) := by
    rw [← heq, LatticePolygon.edgeDir]; module
  exact add_left_cancel this

/-- **Complete reflex-safe off-boundary criterion.** Every point of `sectorCap i lo hi capR`
is off the boundary (for `capR ≤ featureSize`), provided each interior angle `θ ∈ (lo,hi)`
makes `dirOf θ` avoid **both boundary rays**: it is not a nonnegative multiple of `−edgeDir i`
(edge `i`'s ray from `v`) nor of `edgeDir(i+1)` (edge `i+1`'s ray from `v`). This handles the
two collinear-interior directions `+edgeDir i`, `−edgeDir(i+1)` that the cross criterion
cannot, by the beyond-endpoint argument. Non-incident edges via `featureSize_le`. -/
lemma sectorCap_subset_compl_boundary' (i : ZMod P.n) {lo hi capR : ℝ}
    (hRfs : capR ≤ P.featureSize)
    (hrayL : ∀ θ ∈ Set.Ioo lo hi, ∀ s : ℝ, 0 ≤ s → dirOf θ ≠ s • (-(P.edgeDir i)))
    (hrayR : ∀ θ ∈ Set.Ioo lo hi, ∀ s : ℝ, 0 ≤ s → dirOf θ ≠ s • P.edgeDir (i + 1)) :
    P.sectorCap i lo hi capR ⊆ P.boundaryᶜ := by
  intro q hq
  obtain ⟨⟨θ, r⟩, ⟨hθ, hr0, hrR⟩, rfl⟩ := hq
  rw [Set.mem_compl_iff, LatticePolygon.boundary, Set.mem_iUnion]
  rintro ⟨j, hmemj⟩
  simp only [LatticePolygon.sectorMap] at hmemj ⊢
  by_cases hji : j = i
  · subst hji
    refine notMem_edgeSeg_self_of_not_ray P j (fun s hs0 heq => ?_) hmemj
    -- r • dirOf θ = s • (-edgeDir j) ⟹ dirOf θ = (s/r) • (-edgeDir j), contradicting hrayL
    apply hrayL θ hθ (s / r) (by positivity)
    have hsm : r • dirOf θ = r • ((s / r) • (-(P.edgeDir j))) := by
      rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hr0)]; exact heq
    exact smul_right_injective _ (ne_of_gt hr0) hsm
  · by_cases hji1 : j = i + 1
    · subst hji1
      refine notMem_edgeSeg_succ_of_not_ray P i (fun s hs0 heq => ?_) hmemj
      apply hrayR θ hθ (s / r) (by positivity)
      have hsm : r • dirOf θ = r • ((s / r) • P.edgeDir (i + 1)) := by
        rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hr0)]; exact heq
      exact smul_right_injective _ (ne_of_gt hr0) hsm
    · have hfs : P.featureSize ≤ Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j) :=
        featureSize_le P (i + 1) j hji1 (by rw [add_sub_cancel_right]; exact hji)
      have hle : Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j)
          ≤ dist (toReal (P.vert (i + 1))) (toReal (P.vert (i + 1)) + r • dirOf θ) :=
        Metric.infDist_le_dist_of_mem hmemj
      rw [dist_eq_norm, show toReal (P.vert (i + 1)) - (toReal (P.vert (i + 1)) + r • dirOf θ)
          = -(r • dirOf θ) from by abel, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr0] at hle
      have hd1 : r * ‖dirOf θ‖ ≤ r * 1 :=
        mul_le_mul_of_nonneg_left (norm_dirOf_le θ) (le_of_lt hr0)
      rw [mul_one] at hd1
      linarith


/-! ### Angle bookkeeping mod 2π: the two-ray sector split at a vertex

The angular wedge `(0, 2π)` of directions around the vertex `v = vert(i+1)` is bounded
by the two boundary rays `−edgeDir i` (the incoming edge reversed) and `edgeDir (i+1)`
(the outgoing edge). These are distinct rays (`edgeDir_not_antiparallel`), so the wedge
splits into two open sectors at the second ray. The `dirOf`/`argOf` ↔ `Real.Angle`
dictionary below converts "positively parallel to a ray" into "angle ≡ that ray's argument
mod 2π", which the `toIcoMod`/`toIcoMod_mem_Ico` API turns into interval membership. -/

/-- **Equal angles give equal directions.** If `θ ≡ φ` as `Real.Angle` (i.e. mod 2π),
then `dirOf θ = dirOf φ`, since `cos`/`sin` descend to `Real.Angle`. -/
theorem dirOf_eq_of_angle_eq {θ φ : ℝ} (h : (↑θ : Real.Angle) = ↑φ) : dirOf θ = dirOf φ := by
  unfold dirOf
  rw [show Real.cos θ = Real.cos φ from by rw [← Real.Angle.cos_coe, ← Real.Angle.cos_coe, h],
    show Real.sin θ = Real.sin φ from by rw [← Real.Angle.sin_coe, ← Real.Angle.sin_coe, h]]

/-- **Positively-parallel directions have equal angle mod 2π.** If `dirOf θ = s • d` for a
nonzero `d` and some `s ≥ 0`, then `(↑θ : Real.Angle) = ↑(argOf d)`. (Taking Euclidean norm
forces `s = (eDist d)⁻¹ > 0`, so `dirOf θ = dirOf (argOf d)`; then `cos_sin_inj`.) -/
theorem dirOf_pos_parallel {θ : ℝ} {d : ℝ × ℝ} (hd : d ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (heq : dirOf θ = s • d) : (↑θ : Real.Angle) = ↑(argOf d) := by
  have hdir : dirOf (argOf d) = (eDist d)⁻¹ • d := dirOf_argOf hd
  have hedpos : 0 < eDist d := by
    rcases lt_or_eq_of_le (eDist_nonneg d) with h | h
    · exact h
    · exfalso; apply hd
      have : d.1 ^ 2 + d.2 ^ 2 = 0 := by
        have := h.symm; rw [eDist, Real.sqrt_eq_zero (by positivity)] at this; exact this
      exact Prod.ext (show d.1 = 0 by nlinarith [sq_nonneg d.1, sq_nonneg d.2])
        (show d.2 = 0 by nlinarith [sq_nonneg d.1, sq_nonneg d.2])
  have hed1 : eDist (dirOf θ) = 1 := by
    unfold eDist dirOf
    rw [show (Real.cos θ, Real.sin θ).1 ^ 2 + (Real.cos θ, Real.sin θ).2 ^ 2 = 1 from by
      simp [Real.cos_sq_add_sin_sq]]
    exact Real.sqrt_one
  rw [heq, eDist_smul, abs_of_nonneg hs] at hed1
  have hsval : s = (eDist d)⁻¹ := by field_simp at hed1 ⊢; linarith [hed1]
  have hde : dirOf θ = dirOf (argOf d) := by rw [heq, hsval, hdir]
  have hcos : Real.cos θ = Real.cos (argOf d) := by
    have := congrArg Prod.fst hde; simpa [dirOf] using this
  have hsin : Real.sin θ = Real.sin (argOf d) := by
    have := congrArg Prod.snd hde; simpa [dirOf] using this
  exact Real.Angle.cos_sin_inj hcos hsin

/-- **Equal angles ⟹ positively parallel.** The converse of `dirOf_pos_parallel` at the
level of two nonzero vectors: if `argOf a` and `argOf b` are equal mod 2π, then `b = s • a`
for some `s > 0` (`s = eDist b / eDist a`). -/
theorem angle_eq_pos_parallel {a b : ℝ × ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (↑(argOf a) : Real.Angle) = ↑(argOf b)) : ∃ s : ℝ, 0 < s ∧ b = s • a := by
  have hda : dirOf (argOf a) = (eDist a)⁻¹ • a := dirOf_argOf ha
  have hdb : dirOf (argOf b) = (eDist b)⁻¹ • b := dirOf_argOf hb
  have hdeq : dirOf (argOf a) = dirOf (argOf b) := dirOf_eq_of_angle_eq h
  have hedapos : 0 < eDist a := by
    rcases lt_or_eq_of_le (eDist_nonneg a) with h2 | h2
    · exact h2
    · exfalso; apply ha
      have : a.1 ^ 2 + a.2 ^ 2 = 0 := by
        have := h2.symm; rw [eDist, Real.sqrt_eq_zero (by positivity)] at this; exact this
      exact Prod.ext (show a.1 = 0 by nlinarith [sq_nonneg a.1, sq_nonneg a.2])
        (show a.2 = 0 by nlinarith [sq_nonneg a.1, sq_nonneg a.2])
  have hedbpos : 0 < eDist b := by
    rcases lt_or_eq_of_le (eDist_nonneg b) with h2 | h2
    · exact h2
    · exfalso; apply hb
      have : b.1 ^ 2 + b.2 ^ 2 = 0 := by
        have := h2.symm; rw [eDist, Real.sqrt_eq_zero (by positivity)] at this; exact this
      exact Prod.ext (show b.1 = 0 by nlinarith [sq_nonneg b.1, sq_nonneg b.2])
        (show b.2 = 0 by nlinarith [sq_nonneg b.1, sq_nonneg b.2])
  refine ⟨eDist b / eDist a, by positivity, ?_⟩
  have hcancel : (eDist a)⁻¹ • a = (eDist b)⁻¹ • b := by rw [← hda, ← hdb, hdeq]
  have h2 : b = (eDist b) • ((eDist a)⁻¹ • a) := by
    rw [hcancel, smul_smul, mul_inv_cancel₀ (ne_of_gt hedbpos), one_smul]
  nth_rewrite 1 [h2]
  rw [smul_smul, div_eq_mul_inv]

/-- **The two boundary rays at vertex `i+1` are distinct directions.** `edgeDir (i+1)`
(outgoing) is not positively parallel to `−edgeDir i` (incoming reversed); equivalently
their arguments differ mod 2π. Positive parallelism would say `edgeDir (i+1) = (−s) • edgeDir i`
with `s > 0`, exactly the antiparallel relation excluded by `edgeDir_not_antiparallel`. -/
theorem ray_distinct (hsimple : P.IsSimple) (i : ZMod P.n) :
    (↑(argOf (-(P.edgeDir i))) : Real.Angle) ≠ ↑(argOf (P.edgeDir (i + 1))) := by
  intro hcontra
  have hni : (-(P.edgeDir i)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero]; exact edgeDir_ne_zero P hsimple i
  have hni1 : P.edgeDir (i + 1) ≠ 0 := edgeDir_ne_zero P hsimple (i + 1)
  obtain ⟨s, hs, hseq⟩ := angle_eq_pos_parallel hni hni1 hcontra
  exact edgeDir_not_antiparallel P hsimple i ⟨s, hs, by rw [hseq, smul_neg, neg_smul]⟩

/-! ### The two sectors at vertex `i+1`

`α i = argOf (−edgeDir i)` is the angle of the incoming boundary ray; `β i` is the angle of
the outgoing ray `edgeDir (i+1)`, lifted into `(α i, α i + 2π)` via `toIocMod`. The wedge
`(α i, α i + 2π)` splits at `β i` into sector A `= (α i, β i)` and sector B `= (β i, α i + 2π)`. -/

/-- The angle of the incoming boundary ray (`−edgeDir i`) at vertex `i+1`. -/
noncomputable def LatticePolygon.alpha (i : ZMod P.n) : ℝ := argOf (-(P.edgeDir i))

/-- The angle of the outgoing boundary ray (`edgeDir (i+1)`), lifted into `(α i, α i + 2π)`. -/
noncomputable def LatticePolygon.beta (i : ZMod P.n) : ℝ :=
  toIocMod (by positivity : (0:ℝ) < 2 * Real.pi) (P.alpha i) (argOf (P.edgeDir (i + 1)))

/-- `α i < β i`: the second ray's lifted angle is strictly above `α i`. -/
lemma alpha_lt_beta (i : ZMod P.n) : P.alpha i < P.beta i :=
  (toIocMod_mem_Ioc (by positivity : (0:ℝ) < 2 * Real.pi) (P.alpha i)
    (argOf (P.edgeDir (i + 1)))).1

/-- `β i ≤ α i + 2π`. -/
lemma beta_le_alpha_add_2pi (i : ZMod P.n) : P.beta i ≤ P.alpha i + 2 * Real.pi :=
  (toIocMod_mem_Ioc (by positivity : (0:ℝ) < 2 * Real.pi) (P.alpha i)
    (argOf (P.edgeDir (i + 1)))).2

/-- `β i < α i + 2π`: strict, because `β i = α i + 2π` would force the two boundary rays to
coincide (`argOf (edgeDir (i+1)) ≡ α i [PMOD 2π]`), contradicting `ray_distinct`. -/
lemma beta_lt_alpha_add_2pi (hsimple : P.IsSimple) (i : ZMod P.n) :
    P.beta i < P.alpha i + 2 * Real.pi := by
  rcases lt_or_eq_of_le (beta_le_alpha_add_2pi P i) with h | h
  · exact h
  · exfalso
    -- β = α + 2π forces argOf(edgeDir(i+1)) ≡ α [PMOD 2π], i.e. the angles coincide
    have hp : (0:ℝ) < 2 * Real.pi := by positivity
    have hcong : toIocMod hp (P.alpha i) (argOf (P.edgeDir (i + 1))) = P.alpha i + 2 * Real.pi := by
      simp only [LatticePolygon.beta] at h; exact h
    obtain ⟨_, z, hz⟩ := (toIocMod_eq_iff hp (a := P.alpha i) (b := argOf (P.edgeDir (i + 1)))
      (c := P.alpha i + 2 * Real.pi)).mp hcong
    -- contradict ray_distinct: argOf(−edgeDir i) = argOf(edgeDir(i+1)) as Real.Angle
    apply ray_distinct P hsimple i
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    show ∃ k : ℤ, argOf (-(P.edgeDir i)) - argOf (P.edgeDir (i + 1)) = 2 * Real.pi * k
    rw [zsmul_eq_mul] at hz
    refine ⟨-(z + 1), ?_⟩
    have halpha : P.alpha i = argOf (-(P.edgeDir i)) := rfl
    rw [← halpha]; push_cast; linarith [hz]

/-- **The angle `β i` represents the outgoing ray direction mod 2π.** -/
theorem beta_angle_eq (i : ZMod P.n) :
    (↑(P.beta i) : Real.Angle) = ↑(argOf (P.edgeDir (i + 1))) := by
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  have hsub := self_sub_toIocMod hp (P.alpha i) (argOf (P.edgeDir (i + 1)))
  refine ⟨- toIocDiv hp (P.alpha i) (argOf (P.edgeDir (i + 1))), ?_⟩
  simp only [LatticePolygon.beta]
  rw [zsmul_eq_mul] at hsub; push_cast; linarith [hsub]

/-- `edgeDir i = -(eDist (edgeDir i)) • dirOf (α i)`: the edge direction is the negative
Euclidean-length multiple of the unit incoming-reversed ray direction. -/
lemma edgeDir_eq_neg_smul_dirOf_alpha (hsimple : P.IsSimple) (i : ZMod P.n) :
    P.edgeDir i = (-(eDist (P.edgeDir i))) • dirOf (P.alpha i) := by
  have hne : (-(P.edgeDir i)) ≠ 0 := by simp only [ne_eq, neg_eq_zero]; exact edgeDir_ne_zero P hsimple i
  have heD : eDist (-(P.edgeDir i)) = eDist (P.edgeDir i) := by simp [eDist]
  rw [LatticePolygon.alpha, dirOf_argOf hne, heD, smul_smul, neg_mul,
    mul_inv_cancel₀ (ne_of_gt (by rw [eDist]; exact Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple i))), neg_smul, one_smul, neg_neg]

/-- `edgeDir (i+1) = eDist (edgeDir (i+1)) • dirOf (β i)`: the outgoing edge direction is the
*positive* Euclidean-length multiple of the unit outgoing ray direction `dirOf (β i)`. -/
lemma edgeDir_succ_eq_smul_dirOf_beta (hsimple : P.IsSimple) (i : ZMod P.n) :
    P.edgeDir (i + 1) = eDist (P.edgeDir (i + 1)) • dirOf (P.beta i) := by
  have hne : P.edgeDir (i + 1) ≠ 0 := edgeDir_ne_zero P hsimple (i + 1)
  have hdir : dirOf (P.beta i) = (eDist (P.edgeDir (i + 1)))⁻¹ • P.edgeDir (i + 1) := by
    rw [dirOf_eq_of_angle_eq (beta_angle_eq P i), dirOf_argOf hne]
  have heDne : eDist (P.edgeDir (i + 1)) ≠ 0 := by
    rw [eDist]; exact ne_of_gt (Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple (i + 1)))
  rw [hdir, smul_smul, mul_inv_cancel₀ heDne, one_smul]

/-- `cross (c • u) v = c * cross u v`. -/
lemma cross_smul_left (c : ℝ) (u v : ℝ × ℝ) : cross (c • u) v = c * cross u v := by
  simp [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `cross (dirOf α) (dirOf θ) = sin (θ − α)`. -/
lemma cross_dirOf_dirOf (α θ : ℝ) : cross (dirOf α) (dirOf θ) = Real.sin (θ - α) := by
  simp only [cross, dirOf, Real.sin_sub]; ring

/-- `⟨dirOf α, dirOf θ⟩ = cos (θ − α)` (Euclidean inner product). -/
lemma inner_dirOf_dirOf (α θ : ℝ) :
    (dirOf α).1 * (dirOf θ).1 + (dirOf α).2 * (dirOf θ).2 = Real.cos (θ - α) := by
  simp only [dirOf, Real.cos_sub]; ring

/-- `(c • u) ⬝ v = c * (u ⬝ v)` (Euclidean inner product, first slot). -/
lemma inner_smul_left (c : ℝ) (u v : ℝ × ℝ) :
    (c • u).1 * v.1 + (c • u).2 * v.2 = c * (u.1 * v.1 + u.2 * v.2) := by
  simp [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **Two distinct angles within one 2π-period have distinct directions (mod 2π).** -/
theorem angle_ne_of_lt_period {lo θ φ : ℝ} (hθlo : lo ≤ θ) (hθhi : θ < lo + 2 * Real.pi)
    (hφlo : lo ≤ φ) (hφhi : φ < lo + 2 * Real.pi) (hne : θ ≠ φ) :
    (↑θ : Real.Angle) ≠ ↑φ := by
  intro hcontra
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hcontra
  obtain ⟨k, hk⟩ := hcontra
  have hpi : 0 < Real.pi := Real.pi_pos
  have hkz : k = 0 := by
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · exfalso; have : (k:ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hk0
      nlinarith [hk, this]
    · exact hk0
    · exfalso; have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk0
      nlinarith [hk, this]
  rw [hkz] at hk; push_cast at hk; exact hne (by linarith [hk])

/-- **Off-ray, incoming side.** For an angle `θ` within the period `[α i, α i + 2π)` with
`θ ≠ α i`, the direction `dirOf θ` is not a nonnegative multiple of `−edgeDir i`. -/
lemma dirOf_not_ray_incoming (hsimple : P.IsSimple) {i : ZMod P.n} {θ : ℝ} (hlo : P.alpha i ≤ θ)
    (hhi : θ < P.alpha i + 2 * Real.pi) (hne : θ ≠ P.alpha i) (s : ℝ) (hs : 0 ≤ s) :
    dirOf θ ≠ s • (-(P.edgeDir i)) := by
  intro heq
  have hni : (-(P.edgeDir i)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero]; exact edgeDir_ne_zero P hsimple i
  have hang : (↑θ : Real.Angle) = ↑(P.alpha i) := dirOf_pos_parallel hni hs heq
  exact angle_ne_of_lt_period hlo hhi (le_of_eq rfl) (by linarith [Real.pi_pos]) hne hang

/-- **Off-ray, outgoing side.** For an angle `θ` within the period `[α i, α i + 2π)` with
`θ ≠ β i`, the direction `dirOf θ` is not a nonnegative multiple of `edgeDir (i+1)`. -/
lemma dirOf_not_ray_outgoing (hsimple : P.IsSimple) {i : ZMod P.n} {θ : ℝ} (hlo : P.alpha i ≤ θ)
    (hhi : θ < P.alpha i + 2 * Real.pi) (hne : θ ≠ P.beta i) (s : ℝ) (hs : 0 ≤ s) :
    dirOf θ ≠ s • P.edgeDir (i + 1) := by
  intro heq
  have hni : P.edgeDir (i + 1) ≠ 0 := edgeDir_ne_zero P hsimple (i + 1)
  have hang : (↑θ : Real.Angle) = ↑(argOf (P.edgeDir (i + 1))) := dirOf_pos_parallel hni hs heq
  rw [← beta_angle_eq] at hang
  exact angle_ne_of_lt_period hlo hhi (le_of_lt (alpha_lt_beta P i))
    (beta_lt_alpha_add_2pi P hsimple i) hne hang

/-! ### The two corner sector caps at vertex `i+1`

`capA i capR = sectorCap i (α i) (β i) capR` is the wedge of directions strictly between the
incoming ray `α i` and the outgoing ray `β i`; `capB i capR = sectorCap i (β i) (α i + 2π) capR`
is the complementary wedge. Together they fill the full punctured neighbourhood of the vertex
(off the two boundary rays). Each is path-connected and off-boundary. -/

/-- **Sector cap A**: the wedge `(α i, β i)` of directions at vertex `i+1`. -/
noncomputable def LatticePolygon.capA (i : ZMod P.n) (capR : ℝ) : Set (ℝ × ℝ) :=
  P.sectorCap i (P.alpha i) (P.beta i) capR

/-- **Sector cap B**: the wedge `(β i, α i + 2π)` of directions at vertex `i+1`. -/
noncomputable def LatticePolygon.capB (i : ZMod P.n) (capR : ℝ) : Set (ℝ × ℝ) :=
  P.sectorCap i (P.beta i) (P.alpha i + 2 * Real.pi) capR

/-- **`capA i capR` is path-connected** (for `capR > 0`). -/
lemma isPathConnected_capA (_hsimple : P.IsSimple) (i : ZMod P.n) {capR : ℝ} (hR : 0 < capR) :
    IsPathConnected (P.capA i capR) :=
  isPathConnected_sectorCap P i (alpha_lt_beta P i) hR

/-- **`capB i capR` is path-connected** (for `capR > 0`). -/
lemma isPathConnected_capB (hsimple : P.IsSimple) (i : ZMod P.n) {capR : ℝ} (hR : 0 < capR) :
    IsPathConnected (P.capB i capR) :=
  isPathConnected_sectorCap P i (beta_lt_alpha_add_2pi P hsimple i) hR

/-- **`capA i capR ⊆ boundaryᶜ`** (for `capR ≤ featureSize`). Each interior angle `θ ∈ (α i, β i)`
avoids both boundary rays: `θ ≠ α i` (left endpoint) ⟹ off the incoming ray, and `θ < β i`
⟹ off the outgoing ray. -/
lemma capA_subset_compl_boundary (hsimple : P.IsSimple) (i : ZMod P.n) {capR : ℝ}
    (hRfs : capR ≤ P.featureSize) : P.capA i capR ⊆ P.boundaryᶜ := by
  apply sectorCap_subset_compl_boundary' P i hRfs
  · intro θ hθ s hs
    refine dirOf_not_ray_incoming P hsimple (le_of_lt hθ.1)
      (lt_trans hθ.2 (beta_lt_alpha_add_2pi P hsimple i)) (ne_of_gt hθ.1) s hs
  · intro θ hθ s hs
    refine dirOf_not_ray_outgoing P hsimple (le_of_lt hθ.1)
      (lt_trans hθ.2 (beta_lt_alpha_add_2pi P hsimple i)) (ne_of_lt hθ.2) s hs

/-- **`capB i capR ⊆ boundaryᶜ`** (for `capR ≤ featureSize`). Each interior angle
`θ ∈ (β i, α i + 2π)` avoids both boundary rays: `θ > β i > α i` ⟹ off the incoming ray,
and `θ > β i` ⟹ off the outgoing ray. -/
lemma capB_subset_compl_boundary (hsimple : P.IsSimple) (i : ZMod P.n) {capR : ℝ}
    (hRfs : capR ≤ P.featureSize) : P.capB i capR ⊆ P.boundaryᶜ := by
  apply sectorCap_subset_compl_boundary' P i hRfs
  · intro θ hθ s hs
    refine dirOf_not_ray_incoming P hsimple
      (le_of_lt (lt_trans (alpha_lt_beta P i) hθ.1)) hθ.2
      (ne_of_gt (lt_trans (alpha_lt_beta P i) hθ.1)) s hs
  · intro θ hθ s hs
    refine dirOf_not_ray_outgoing P hsimple
      (le_of_lt (lt_trans (alpha_lt_beta P i) hθ.1)) hθ.2 (ne_of_gt hθ.1) s hs

/-! ### The 2-coloring of directions at a vertex

A direction `w` off both boundary rays has its angle (lifted into `[α i, α i + 2π)`) landing
strictly inside exactly one of the two sectors `(α i, β i)` or `(β i, α i + 2π)`. -/

/-- **`toIcoMod` preserves the `Real.Angle` class** (lift into one period is ≡ mod 2π). -/
theorem toIcoMod_angle_eq (lo b : ℝ) :
    (↑(toIcoMod (by positivity : (0:ℝ) < 2 * Real.pi) lo b) : Real.Angle) = ↑b := by
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  obtain ⟨_, z, hz⟩ := (toIcoMod_eq_iff hp (a := lo) (b := b) (c := toIcoMod hp lo b)).mp rfl
  refine ⟨-z, ?_⟩; rw [zsmul_eq_mul] at hz; push_cast; linarith [hz]

/-- **Two-coloring.** A direction `w` whose angle is `≢ α i` and `≢ β i` (mod 2π) has its
lifted angle `toIcoMod 2π (α i) (argOf w)` strictly inside sector A `(α i, β i)` or sector B
`(β i, α i + 2π)`. -/
theorem two_coloring (i : ZMod P.n) {w : ℝ × ℝ}
    (hneα : (↑(argOf w) : Real.Angle) ≠ ↑(P.alpha i))
    (hneβ : (↑(argOf w) : Real.Angle) ≠ ↑(P.beta i)) :
    (toIcoMod (by positivity : (0:ℝ) < 2 * Real.pi) (P.alpha i) (argOf w))
        ∈ Set.Ioo (P.alpha i) (P.beta i) ∨
    (toIcoMod (by positivity : (0:ℝ) < 2 * Real.pi) (P.alpha i) (argOf w))
        ∈ Set.Ioo (P.beta i) (P.alpha i + 2 * Real.pi) := by
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  set x := toIcoMod hp (P.alpha i) (argOf w) with hx
  have hmem : x ∈ Set.Ico (P.alpha i) (P.alpha i + 2 * Real.pi) :=
    toIcoMod_mem_Ico hp (P.alpha i) (argOf w)
  have hxa : (↑x : Real.Angle) = ↑(argOf w) := toIcoMod_angle_eq (P.alpha i) (argOf w)
  have hxnea : x ≠ P.alpha i := by intro h; apply hneα; rw [← hxa, h]
  have hxneb : x ≠ P.beta i := by intro h; apply hneβ; rw [← hxa, h]
  rcases lt_trichotomy x (P.beta i) with hlt | heq | hgt
  · left; exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxnea), hlt⟩
  · exact absurd heq hxneb
  · right; exact ⟨hgt, hmem.2⟩

/-- **Membership in a sector cap via any angle representative.** If `θ ∈ (lo, hi)` has the
same direction as `q − v` (`↑θ = ↑(argOf (q − v))` as `Real.Angle`) and `q` is within Euclidean
radius `capR` of the vertex `v = vert(i+1)`, then `q ∈ sectorCap i lo hi capR`. -/
lemma mem_sectorCap_of_repr (i : ZMod P.n) {lo hi capR θ : ℝ} {q : ℝ × ℝ}
    (hne : q ≠ toReal (P.vert (i + 1)))
    (hθmem : θ ∈ Set.Ioo lo hi)
    (hθeq : (↑θ : Real.Angle) = ↑(argOf (q - toReal (P.vert (i + 1)))))
    (hball : eDist (q - toReal (P.vert (i + 1))) < capR) :
    q ∈ P.sectorCap i lo hi capR := by
  set v := toReal (P.vert (i + 1)) with hv
  set w := q - v with hw
  have hwne : w ≠ 0 := sub_ne_zero.mpr hne
  have hepos : 0 < eDist w := by
    rcases lt_or_eq_of_le (eDist_nonneg w) with h | h
    · exact h
    · exfalso; apply hwne
      have : w.1 ^ 2 + w.2 ^ 2 = 0 := by
        have := h.symm; rw [eDist, Real.sqrt_eq_zero (by positivity)] at this; exact this
      exact Prod.ext (show w.1 = 0 by nlinarith [sq_nonneg w.1, sq_nonneg w.2])
        (show w.2 = 0 by nlinarith [sq_nonneg w.1, sq_nonneg w.2])
  have hdir : dirOf θ = (eDist w)⁻¹ • w := by
    rw [dirOf_eq_of_angle_eq hθeq, dirOf_argOf hwne]
  refine ⟨(θ, eDist w), ⟨hθmem, hepos, hball⟩, ?_⟩
  simp only [LatticePolygon.sectorMap]
  rw [hdir, smul_smul, mul_inv_cancel₀ (ne_of_gt hepos), one_smul, hw]; abel

/-- **Vertex cover step.** A point `q ≠ vert(i+1)` within Euclidean radius `capR` of the
vertex `vert(i+1)`, whose offset direction avoids both boundary rays (`↑(argOf (q−v)) ≠ α i, β i`
as `Real.Angle`), lies in `capA i capR` or `capB i capR`. The 2-coloring picks the sector; the
`toIcoMod`-lifted angle is the representative. -/
lemma mem_capA_or_capB (i : ZMod P.n) {capR : ℝ} {q : ℝ × ℝ}
    (hne : q ≠ toReal (P.vert (i + 1)))
    (hneα : (↑(argOf (q - toReal (P.vert (i + 1)))) : Real.Angle) ≠ ↑(P.alpha i))
    (hneβ : (↑(argOf (q - toReal (P.vert (i + 1)))) : Real.Angle) ≠ ↑(P.beta i))
    (hball : eDist (q - toReal (P.vert (i + 1))) < capR) :
    q ∈ P.capA i capR ∨ q ∈ P.capB i capR := by
  have heq := toIcoMod_angle_eq (P.alpha i) (argOf (q - toReal (P.vert (i + 1))))
  rcases two_coloring P i hneα hneβ with hA | hB
  · left
    exact mem_sectorCap_of_repr P i hne hA heq hball
  · right
    exact mem_sectorCap_of_repr P i hne hB heq hball

/-! ### Foot near an adjacent edge forces the foot near the shared vertex

The cover dichotomy needs: when the perpendicular foot `foot i s` of an off-boundary point
is close to an *adjacent* edge `j`, it is actually close to the shared vertex (so the point
lands in a corner cap). The quantitative engine is the perpendicular-distance lower bound:
the signed distance to the *line* of edge `j` is `≤` the distance to the segment, and it is
a `1`-Lipschitz (after dividing by `|d.1|+|d.2|`) linear functional vanishing on edge `j`. -/

/-- **Perpendicular-distance lower bound.** For every point `p`, the cross product
`cross (edgeDir j) (p − vert j)` (signed distance to the line of edge `j`, up to scale) is
bounded by `(|d.1|+|d.2|)·infDist p (edgeSeg j)`. Every `y ∈ edgeSeg j` is on the edge line
(`cross (edgeDir j) (y − vert j) = 0`), so `|cross (edgeDir j) (p−vert j)| =
|cross (edgeDir j) (p−y)| ≤ (|d.1|+|d.2|)·dist p y`; take the infimum. -/
lemma abs_cross_le_infDist (j : ZMod P.n) (p : ℝ × ℝ) :
    |cross (P.edgeDir j) (p - toReal (P.vert j))|
      ≤ (|(P.edgeDir j).1| + |(P.edgeDir j).2|) * Metric.infDist p (P.edgeSeg j) := by
  have hcross_bd : ∀ w : ℝ × ℝ,
      |cross (P.edgeDir j) w| ≤ (|(P.edgeDir j).1| + |(P.edgeDir j).2|) * ‖w‖ := by
    intro w
    rw [cross, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |w.1| ≤ max |w.1| |w.2| := le_max_left _ _
    have h2 : |w.2| ≤ max |w.1| |w.2| := le_max_right _ _
    calc |(P.edgeDir j).1 * w.2 - (P.edgeDir j).2 * w.1|
          ≤ |(P.edgeDir j).1 * w.2| + |(P.edgeDir j).2 * w.1| := abs_sub _ _
      _ = |(P.edgeDir j).1| * |w.2| + |(P.edgeDir j).2| * |w.1| := by rw [abs_mul, abs_mul]
      _ ≤ (|(P.edgeDir j).1| + |(P.edgeDir j).2|) * max |w.1| |w.2| := by
          nlinarith [abs_nonneg (P.edgeDir j).1, abs_nonneg (P.edgeDir j).2, h1, h2]
  set C := |(P.edgeDir j).1| + |(P.edgeDir j).2| with hC
  have hCnn : 0 ≤ C := by positivity
  have hne : (P.edgeSeg j).Nonempty :=
    ⟨toReal (P.vert j), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩
  rcases eq_or_lt_of_le hCnn with hC0 | hCpos
  · have hz : cross (P.edgeDir j) (p - toReal (P.vert j)) = 0 := by
      have := hcross_bd (p - toReal (P.vert j))
      rw [← hC0] at this; simp only [zero_mul] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    rw [hz, abs_zero, ← hC0, zero_mul]
  · have key : |cross (P.edgeDir j) (p - toReal (P.vert j))| / C
        ≤ Metric.infDist p (P.edgeSeg j) := by
      rw [Metric.le_infDist hne]
      intro y hy
      have hyline : cross (P.edgeDir j) (y - toReal (P.vert j)) = 0 := by
        rw [LatticePolygon.edgeSeg, segment_eq_image] at hy
        obtain ⟨u, _, rfl⟩ := hy
        simp only [LatticePolygon.edgeDir, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
      have hsplit : cross (P.edgeDir j) (p - toReal (P.vert j)) = cross (P.edgeDir j) (p - y) := by
        rw [← sub_eq_zero,
          ← (isLinearMap_cross (P.edgeDir j)).map_sub (p - toReal (P.vert j)) (p - y),
          show (p - toReal (P.vert j)) - (p - y) = y - toReal (P.vert j) from by abel, hyline]
      rw [hsplit, dist_eq_norm, div_le_iff₀ hCpos]
      calc |cross (P.edgeDir j) (p - y)| ≤ C * ‖p - y‖ := hcross_bd _
        _ = ‖p - y‖ * C := by ring
    rw [div_le_iff₀ hCpos] at key; linarith [key]

/-- **Collinear-forward extraction.** If the successor edge direction is collinear with
edge `i`'s (`cross (edgeDir (i+1)) (edgeDir i) = 0`), it is a *nonnegative* multiple of it:
the antiparallel (negative) case is ruled out by `edgeDir_not_antiparallel`. -/
lemma edgeDir_succ_nonneg_smul_of_cross_zero (hsimple : P.IsSimple) (i : ZMod P.n)
    (hcol : cross (P.edgeDir (i + 1)) (P.edgeDir i) = 0) :
    ∃ μ : ℝ, 0 ≤ μ ∧ P.edgeDir (i + 1) = μ • P.edgeDir i := by
  have hNpos : 0 < (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 := normSq_edgeDir_pos P hsimple i
  have hNne : (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 ≠ 0 := ne_of_gt hNpos
  have hc : (P.edgeDir (i + 1)).1 * (P.edgeDir i).2
      - (P.edgeDir (i + 1)).2 * (P.edgeDir i).1 = 0 := hcol
  have hpar : P.edgeDir (i + 1) = (((P.edgeDir (i + 1)).1 * (P.edgeDir i).1
      + (P.edgeDir (i + 1)).2 * (P.edgeDir i).2)
      / ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2)) • P.edgeDir i := by
    apply Prod.ext
    · simp only [Prod.smul_fst, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hNne]
      linear_combination (P.edgeDir i).2 * hc
    · simp only [Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hNne]
      linear_combination -(P.edgeDir i).1 * hc
  refine ⟨_, ?_, hpar⟩
  by_contra hneg
  push Not at hneg
  exact edgeDir_not_antiparallel P hsimple i ⟨-_, by linarith, by rw [neg_neg]; exact hpar⟩

/-- **Vertex is the nearest point of the collinear-forward successor edge.** If
`edgeDir (i+1) = μ • edgeDir i` with `μ ≥ 0` (collinear-forward), the interior foot
`foot i s` (which lies *behind* the shared vertex `vert (i+1)` along edge `i`) has the
vertex as its nearest point of edge `i+1`: `dist (foot i s) (vert (i+1)) ≤
infDist (foot i s) (edgeSeg (i+1))`. -/
lemma dist_vert_le_infDist_succ_of_collinear (i : ZMod P.n) {s : ℝ}
    (hs : s ∈ Set.Ioo (0:ℝ) 1) {μ : ℝ} (hμ : 0 ≤ μ)
    (hcol : P.edgeDir (i + 1) = μ • P.edgeDir i) :
    dist (P.foot i s) (toReal (P.vert (i + 1)))
      ≤ Metric.infDist (P.foot i s) (P.edgeSeg (i + 1)) := by
  rw [Metric.le_infDist ⟨toReal (P.vert (i + 1)),
    by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩]
  intro y hy
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hy
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hy
  simp only []
  have hfoot : P.foot i s = toReal (P.vert (i + 1)) + (-(1 - s)) • P.edgeDir i := by
    rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
  have hyv : ((1 - r) • toReal (P.vert (i + 1)) + r • toReal (P.vert (i + 1 + 1)))
      = toReal (P.vert (i + 1)) + (r * μ) • P.edgeDir i := by
    have hh : toReal (P.vert (i + 1 + 1)) - toReal (P.vert (i + 1)) = P.edgeDir (i + 1) := by
      rw [LatticePolygon.edgeDir]
    rw [hcol] at hh
    rw [show (1 - r) • toReal (P.vert (i + 1)) + r • toReal (P.vert (i + 1 + 1))
        = toReal (P.vert (i + 1)) + r • (toReal (P.vert (i + 1 + 1))
          - toReal (P.vert (i + 1))) from by module, hh, smul_smul]
  rw [dist_eq_norm, dist_eq_norm, hyv, hfoot,
    show (toReal (P.vert (i + 1)) + (-(1 - s)) • P.edgeDir i) - toReal (P.vert (i + 1))
      = (-(1 - s)) • P.edgeDir i from by module,
    show (toReal (P.vert (i + 1)) + (-(1 - s)) • P.edgeDir i)
        - (toReal (P.vert (i + 1)) + (r * μ) • P.edgeDir i)
      = (-(1 - s) - r * μ) • P.edgeDir i from by module,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  have hle : |(-(1 - s))| ≤ |(-(1 - s) - r * μ)| := by
    rw [abs_neg, abs_of_nonneg hs1]
    have hrm : 0 ≤ r * μ := by positivity
    rw [show -(1 - s) - r * μ = -((1 - s) + r * μ) from by ring, abs_neg,
      abs_of_nonneg (by linarith)]
    linarith
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- **Task 1 (successor edge): foot near the successor edge forces foot near the shared
vertex.** For each edge `i` there is a constant `C > 0` such that whenever the interior foot
`foot i s` (`s ∈ (0,1)`) is within `ρ` of the adjacent edge `i+1` (which shares the vertex
`vert (i+1)`), the foot is within `C·ρ` (Euclidean) of that vertex. Two regimes: if the two
edges are non-collinear (`cross ≠ 0`), the perpendicular-distance bound gives `C` from the
ratio `(|d.1|+|d.2|)·eDist(edgeDir i)/|cross|`; if collinear-forward, the vertex *is* the
nearest point of edge `i+1` so `C = √2` suffices. -/
lemma foot_near_succ_edge_near_vertex (hsimple : P.IsSimple) (i : ZMod P.n) :
    ∃ C > 0, ∀ s, s ∈ Set.Ioo (0:ℝ) 1 → ∀ ρ : ℝ,
      Metric.infDist (P.foot i s) (P.edgeSeg (i + 1)) ≤ ρ →
      eDist (P.foot i s - toReal (P.vert (i + 1))) ≤ C * ρ := by
  by_cases hcol : cross (P.edgeDir (i + 1)) (P.edgeDir i) = 0
  · -- collinear-forward: the vertex is the nearest point of edge i+1
    obtain ⟨μ, hμ, hpar⟩ := edgeDir_succ_nonneg_smul_of_cross_zero P hsimple i hcol
    refine ⟨Real.sqrt 2, by positivity, ?_⟩
    intro s hs ρ hρ
    have hdv : dist (P.foot i s) (toReal (P.vert (i + 1))) ≤ ρ :=
      le_trans (dist_vert_le_infDist_succ_of_collinear P i hs hμ hpar) hρ
    calc eDist (P.foot i s - toReal (P.vert (i + 1)))
          ≤ Real.sqrt 2 * dist (P.foot i s) (toReal (P.vert (i + 1))) :=
            eDist_sub_le_sqrt2_dist _ _
      _ ≤ Real.sqrt 2 * ρ := mul_le_mul_of_nonneg_left hdv (by positivity)
  · -- non-collinear: perpendicular-distance bound
    set Cd := |(P.edgeDir (i + 1)).1| + |(P.edgeDir (i + 1)).2| with hCd
    set X := |cross (P.edgeDir (i + 1)) (P.edgeDir i)| with hX
    have hXpos : 0 < X := by rw [hX, abs_pos]; exact hcol
    set ed := eDist (P.edgeDir i) with hed
    have hedpos : 0 < ed := by
      rw [hed, eDist]; exact Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple i)
    have hCdnn : 0 ≤ Cd := by positivity
    have hCdpos : 0 < Cd := by
      rcases lt_or_eq_of_le hCdnn with h | h
      · exact h
      · exfalso
        have h1 : (P.edgeDir (i + 1)).1 = 0 := by
          have := abs_nonneg (P.edgeDir (i + 1)).1
          have := abs_nonneg (P.edgeDir (i + 1)).2
          have : |(P.edgeDir (i + 1)).1| = 0 := by rw [hCd] at h; linarith
          exact abs_eq_zero.mp this
        have h2 : (P.edgeDir (i + 1)).2 = 0 := by
          have := abs_nonneg (P.edgeDir (i + 1)).1
          have := abs_nonneg (P.edgeDir (i + 1)).2
          have : |(P.edgeDir (i + 1)).2| = 0 := by rw [hCd] at h; linarith
          exact abs_eq_zero.mp this
        exact edgeDir_ne_zero P hsimple (i + 1) (Prod.ext h1 h2)
    refine ⟨Cd * ed / X, by positivity, ?_⟩
    intro s hs ρ hρ
    have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
    have hfv : P.foot i s - toReal (P.vert (i + 1)) = (-(1 - s)) • P.edgeDir i := by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
    have hcrosseq : cross (P.edgeDir (i + 1)) (P.foot i s - toReal (P.vert (i + 1)))
        = (-(1 - s)) * cross (P.edgeDir (i + 1)) (P.edgeDir i) := by
      rw [hfv]; exact (isLinearMap_cross (P.edgeDir (i + 1))).map_smul _ _
    have hbd := abs_cross_le_infDist P (i + 1) (P.foot i s)
    rw [hcrosseq, abs_mul, abs_neg, abs_of_nonneg hs1, ← hX] at hbd
    have hbd2 : (1 - s) * X ≤ Cd * ρ := le_trans hbd (mul_le_mul_of_nonneg_left hρ hCdnn)
    have hedist : eDist (P.foot i s - toReal (P.vert (i + 1))) = (1 - s) * ed := by
      rw [hfv, eDist_smul, abs_neg, abs_of_nonneg hs1]
    rw [hedist, show Cd * ed / X * ρ = (Cd * ρ) * ed / X from by ring, le_div_iff₀ hXpos]
    calc (1 - s) * ed * X = ((1 - s) * X) * ed := by ring
      _ ≤ (Cd * ρ) * ed := mul_le_mul_of_nonneg_right hbd2 (le_of_lt hedpos)

/-- **Vertex is the nearest point of the collinear-forward predecessor edge.** Mirror of
`dist_vert_le_infDist_succ_of_collinear`: if `edgeDir i = ν • edgeDir (i-1)` with `ν ≥ 0`,
the interior foot `foot i s` lies *ahead* of the shared vertex `vert i` along edge `i`, so
the vertex is the nearest point of edge `i-1`. -/
lemma dist_vert_le_infDist_pred_of_collinear (i : ZMod P.n) {s : ℝ}
    (hs : s ∈ Set.Ioo (0:ℝ) 1) {ν : ℝ} (hν : 0 ≤ ν)
    (hcol : P.edgeDir i = ν • P.edgeDir (i - 1)) :
    dist (P.foot i s) (toReal (P.vert i))
      ≤ Metric.infDist (P.foot i s) (P.edgeSeg (i - 1)) := by
  have hi : (i - 1) + 1 = i := by ring
  rw [Metric.le_infDist ⟨toReal (P.vert i),
    by rw [LatticePolygon.edgeSeg, hi]; exact right_mem_segment ℝ _ _⟩]
  intro y hy
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hy
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hy
  simp only []
  have hfoot : P.foot i s = toReal (P.vert i) + s • P.edgeDir i := by
    rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
  have hyv : ((1 - r) • toReal (P.vert (i - 1)) + r • toReal (P.vert ((i - 1) + 1)))
      = toReal (P.vert i) + (-(1 - r)) • P.edgeDir (i - 1) := by
    rw [hi, show toReal (P.vert (i - 1)) = toReal (P.vert i) - P.edgeDir (i - 1) from by
      rw [LatticePolygon.edgeDir, hi]; abel]
    module
  rw [dist_eq_norm, dist_eq_norm, hyv, hfoot, hcol,
    show (toReal (P.vert i) + s • (ν • P.edgeDir (i - 1))) - toReal (P.vert i)
      = (s * ν) • P.edgeDir (i - 1) from by module,
    show (toReal (P.vert i) + s • (ν • P.edgeDir (i - 1)))
        - (toReal (P.vert i) + (-(1 - r)) • P.edgeDir (i - 1))
      = (s * ν + (1 - r)) • P.edgeDir (i - 1) from by module,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hsv : 0 ≤ s * ν := mul_nonneg (le_of_lt hs.1) hν
  have hle : |s * ν| ≤ |s * ν + (1 - r)| := by
    rw [abs_of_nonneg hsv, abs_of_nonneg (by linarith)]; linarith
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- **Task 1 (predecessor edge): foot near the predecessor edge forces foot near the shared
vertex.** Mirror of `foot_near_succ_edge_near_vertex` for the adjacent edge `i-1`, which
shares vertex `vert i`. The interior foot `foot i s` within `ρ` of edge `i-1` is within
`C·ρ` (Euclidean) of `vert i`. -/
lemma foot_near_pred_edge_near_vertex (hsimple : P.IsSimple) (i : ZMod P.n) :
    ∃ C > 0, ∀ s, s ∈ Set.Ioo (0:ℝ) 1 → ∀ ρ : ℝ,
      Metric.infDist (P.foot i s) (P.edgeSeg (i - 1)) ≤ ρ →
      eDist (P.foot i s - toReal (P.vert i)) ≤ C * ρ := by
  by_cases hcol : cross (P.edgeDir (i - 1)) (P.edgeDir i) = 0
  · -- collinear-forward: extract via the successor lemma at index i-1
    have hcol' : cross (P.edgeDir ((i - 1) + 1)) (P.edgeDir (i - 1)) = 0 := by
      have hi : (i - 1) + 1 = i := by ring
      rw [hi]; rw [cross] at hcol ⊢; linarith
    obtain ⟨μ, hμ, hpar⟩ := edgeDir_succ_nonneg_smul_of_cross_zero P hsimple (i - 1) hcol'
    have hpar' : P.edgeDir i = μ • P.edgeDir (i - 1) := by
      have hi : (i - 1) + 1 = i := by ring
      rw [hi] at hpar; exact hpar
    refine ⟨Real.sqrt 2, by positivity, ?_⟩
    intro s hs ρ hρ
    have hdv : dist (P.foot i s) (toReal (P.vert i)) ≤ ρ :=
      le_trans (dist_vert_le_infDist_pred_of_collinear P i hs hμ hpar') hρ
    calc eDist (P.foot i s - toReal (P.vert i))
          ≤ Real.sqrt 2 * dist (P.foot i s) (toReal (P.vert i)) := eDist_sub_le_sqrt2_dist _ _
      _ ≤ Real.sqrt 2 * ρ := mul_le_mul_of_nonneg_left hdv (by positivity)
  · -- non-collinear: perpendicular-distance bound on edge i-1
    set Cd := |(P.edgeDir (i - 1)).1| + |(P.edgeDir (i - 1)).2| with hCd
    set X := |cross (P.edgeDir (i - 1)) (P.edgeDir i)| with hX
    have hXpos : 0 < X := by rw [hX, abs_pos]; exact hcol
    set ed := eDist (P.edgeDir i) with hed
    have hedpos : 0 < ed := by
      rw [hed, eDist]; exact Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple i)
    have hCdnn : 0 ≤ Cd := by positivity
    have hCdpos : 0 < Cd := by
      rcases lt_or_eq_of_le hCdnn with h | h
      · exact h
      · exfalso
        have h1 : |(P.edgeDir (i - 1)).1| = 0 := by
          rw [hCd] at h; linarith [abs_nonneg (P.edgeDir (i - 1)).1, abs_nonneg (P.edgeDir (i - 1)).2]
        have h2 : |(P.edgeDir (i - 1)).2| = 0 := by
          rw [hCd] at h; linarith [abs_nonneg (P.edgeDir (i - 1)).1, abs_nonneg (P.edgeDir (i - 1)).2]
        exact edgeDir_ne_zero P hsimple (i - 1) (Prod.ext (abs_eq_zero.mp h1) (abs_eq_zero.mp h2))
    refine ⟨Cd * ed / X, by positivity, ?_⟩
    intro s hs ρ hρ
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hi : (i - 1) + 1 = i := by ring
    -- vert i lies on edge (i-1)'s line, so the cross-offset can use vert i
    have hvi : cross (P.edgeDir (i - 1)) (P.foot i s - toReal (P.vert (i - 1)))
        = cross (P.edgeDir (i - 1)) (P.foot i s - toReal (P.vert i)) := by
      have hconst : cross (P.edgeDir (i - 1)) (toReal (P.vert i) - toReal (P.vert (i - 1))) = 0 := by
        rw [show toReal (P.vert i) - toReal (P.vert (i - 1)) = P.edgeDir (i - 1) from by
          rw [LatticePolygon.edgeDir, hi]]
        rw [cross]; ring
      have := (isLinearMap_cross (P.edgeDir (i - 1))).map_sub
        (P.foot i s - toReal (P.vert (i - 1))) (P.foot i s - toReal (P.vert i))
      rw [show (P.foot i s - toReal (P.vert (i - 1))) - (P.foot i s - toReal (P.vert i))
        = toReal (P.vert i) - toReal (P.vert (i - 1)) from by abel, hconst] at this
      linarith [this]
    have hfv : P.foot i s - toReal (P.vert i) = s • P.edgeDir i := by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
    have hcrosseq : cross (P.edgeDir (i - 1)) (P.foot i s - toReal (P.vert (i - 1)))
        = s * cross (P.edgeDir (i - 1)) (P.edgeDir i) := by
      rw [hvi, hfv]; exact (isLinearMap_cross (P.edgeDir (i - 1))).map_smul _ _
    have hbd := abs_cross_le_infDist P (i - 1) (P.foot i s)
    rw [hcrosseq, abs_mul, abs_of_nonneg hs0, ← hX] at hbd
    have hbd2 : s * X ≤ Cd * ρ := le_trans hbd (mul_le_mul_of_nonneg_left hρ hCdnn)
    have hedist : eDist (P.foot i s - toReal (P.vert i)) = s * ed := by
      rw [hfv, eDist_smul, abs_of_nonneg hs0]
    rw [hedist, show Cd * ed / X * ρ = (Cd * ρ) * ed / X from by ring, le_div_iff₀ hXpos]
    calc s * ed * X = (s * X) * ed := by ring
      _ ≤ (Cd * ρ) * ed := mul_le_mul_of_nonneg_right hbd2 (le_of_lt hedpos)

/-- **Lower bound on the distance from an interior foot to the successor edge.** There is a
constant `K > 0` such that for every interior `s ∈ (0,1)`, `K·(1−s) ≤ infDist (foot i s)
(edgeSeg (i+1))`. Non-collinear: the perpendicular cross-distance lower bound; collinear:
the shared vertex `vert (i+1)` is the nearest point and `dist (foot i s) (vert (i+1)) =
(1−s)·‖edgeDir i‖`. This is the reverse of `foot_near_succ_edge_near_vertex`, giving the
binding-edge clearance for the corner meets. -/
lemma infDist_succ_ge (hsimple : P.IsSimple) (i : ZMod P.n) :
    ∃ K > 0, ∀ s, s ∈ Set.Ioo (0:ℝ) 1 →
      K * (1 - s) ≤ Metric.infDist (P.foot i s) (P.edgeSeg (i + 1)) := by
  by_cases hcol : cross (P.edgeDir (i + 1)) (P.edgeDir i) = 0
  · obtain ⟨μ, hμ, hpar⟩ := edgeDir_succ_nonneg_smul_of_cross_zero P hsimple i hcol
    refine ⟨‖P.edgeDir i‖, norm_pos_iff.mpr (edgeDir_ne_zero P hsimple i), ?_⟩
    intro s hs
    have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
    have hv1 : dist (P.foot i s) (toReal (P.vert (i+1))) = (1 - s) * ‖P.edgeDir i‖ := by
      rw [dist_eq_norm, show P.foot i s - toReal (P.vert (i+1)) = (1-s) • (-(P.edgeDir i)) from by
        rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hs1, norm_neg]
    calc ‖P.edgeDir i‖ * (1 - s) = (1 - s) * ‖P.edgeDir i‖ := by ring
      _ = dist (P.foot i s) (toReal (P.vert (i+1))) := hv1.symm
      _ ≤ Metric.infDist (P.foot i s) (P.edgeSeg (i + 1)) :=
          dist_vert_le_infDist_succ_of_collinear P i hs hμ hpar
  · set Cd := |(P.edgeDir (i + 1)).1| + |(P.edgeDir (i + 1)).2| with hCd
    set X := |cross (P.edgeDir (i + 1)) (P.edgeDir i)| with hX
    have hXpos : 0 < X := by rw [hX, abs_pos]; exact hcol
    have hCdpos : 0 < Cd := by
      rcases lt_or_eq_of_le (by positivity : (0:ℝ) ≤ Cd) with h | h
      · exact h
      · exfalso
        have h1 : |(P.edgeDir (i + 1)).1| = 0 := by
          rw [hCd] at h; linarith [abs_nonneg (P.edgeDir (i + 1)).1, abs_nonneg (P.edgeDir (i + 1)).2]
        have h2 : |(P.edgeDir (i + 1)).2| = 0 := by
          rw [hCd] at h; linarith [abs_nonneg (P.edgeDir (i + 1)).1, abs_nonneg (P.edgeDir (i + 1)).2]
        exact edgeDir_ne_zero P hsimple (i + 1) (Prod.ext (abs_eq_zero.mp h1) (abs_eq_zero.mp h2))
    refine ⟨X / Cd, by positivity, ?_⟩
    intro s hs
    have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
    have hfv : P.foot i s - toReal (P.vert (i + 1)) = (-(1 - s)) • P.edgeDir i := by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
    have hcrosseq : cross (P.edgeDir (i + 1)) (P.foot i s - toReal (P.vert (i + 1)))
        = (-(1 - s)) * cross (P.edgeDir (i + 1)) (P.edgeDir i) := by
      rw [hfv]; exact (isLinearMap_cross (P.edgeDir (i + 1))).map_smul _ _
    have hbd := abs_cross_le_infDist P (i + 1) (P.foot i s)
    rw [hcrosseq, abs_mul, abs_neg, abs_of_nonneg hs1, ← hX] at hbd
    rw [div_mul_eq_mul_div, div_le_iff₀ hCdpos]
    calc X * (1 - s) = (1 - s) * X := by ring
      _ ≤ Cd * Metric.infDist (P.foot i s) (P.edgeSeg (i + 1)) := hbd
      _ = Metric.infDist (P.foot i s) (P.edgeSeg (i + 1)) * Cd := by ring

/-- **Lower bound on the distance from an interior foot to the predecessor edge.** Mirror of
`infDist_succ_ge`: there is `K > 0` with `K·s ≤ infDist (foot i s) (edgeSeg (i-1))` for every
interior `s`. The binding factor is `s` (distance from the start vertex `vert i`, which edge
`i-1` shares). This gives the binding-edge clearance for the corner meets that sit near a
*start* vertex. -/
lemma infDist_pred_ge (hsimple : P.IsSimple) (i : ZMod P.n) :
    ∃ K > 0, ∀ s, s ∈ Set.Ioo (0:ℝ) 1 →
      K * s ≤ Metric.infDist (P.foot i s) (P.edgeSeg (i - 1)) := by
  by_cases hcol : cross (P.edgeDir (i - 1)) (P.edgeDir i) = 0
  · have hcol' : cross (P.edgeDir ((i - 1) + 1)) (P.edgeDir (i - 1)) = 0 := by
      have hi : (i - 1) + 1 = i := by ring
      rw [hi]; rw [cross] at hcol ⊢; linarith
    obtain ⟨μ, hμ, hpar⟩ := edgeDir_succ_nonneg_smul_of_cross_zero P hsimple (i - 1) hcol'
    have hpar' : P.edgeDir i = μ • P.edgeDir (i - 1) := by
      have hi : (i - 1) + 1 = i := by ring
      rw [hi] at hpar; exact hpar
    refine ⟨‖P.edgeDir i‖, norm_pos_iff.mpr (edgeDir_ne_zero P hsimple i), ?_⟩
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hv0 : dist (P.foot i s) (toReal (P.vert i)) = s * ‖P.edgeDir i‖ := by
      rw [dist_eq_norm, show P.foot i s - toReal (P.vert i) = s • P.edgeDir i from by
        rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    calc ‖P.edgeDir i‖ * s = s * ‖P.edgeDir i‖ := by ring
      _ = dist (P.foot i s) (toReal (P.vert i)) := hv0.symm
      _ ≤ Metric.infDist (P.foot i s) (P.edgeSeg (i - 1)) :=
          dist_vert_le_infDist_pred_of_collinear P i hs hμ hpar'
  · set Cd := |(P.edgeDir (i - 1)).1| + |(P.edgeDir (i - 1)).2| with hCd
    set X := |cross (P.edgeDir (i - 1)) (P.edgeDir i)| with hX
    have hXpos : 0 < X := by rw [hX, abs_pos]; exact hcol
    have hCdpos : 0 < Cd := by
      rcases lt_or_eq_of_le (by positivity : (0:ℝ) ≤ Cd) with h | h
      · exact h
      · exfalso
        have h1 : |(P.edgeDir (i - 1)).1| = 0 := by
          rw [hCd] at h; linarith [abs_nonneg (P.edgeDir (i - 1)).1, abs_nonneg (P.edgeDir (i - 1)).2]
        have h2 : |(P.edgeDir (i - 1)).2| = 0 := by
          rw [hCd] at h; linarith [abs_nonneg (P.edgeDir (i - 1)).1, abs_nonneg (P.edgeDir (i - 1)).2]
        exact edgeDir_ne_zero P hsimple (i - 1) (Prod.ext (abs_eq_zero.mp h1) (abs_eq_zero.mp h2))
    refine ⟨X / Cd, by positivity, ?_⟩
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hi : (i - 1) + 1 = i := by ring
    have hvi : cross (P.edgeDir (i - 1)) (P.foot i s - toReal (P.vert (i - 1)))
        = cross (P.edgeDir (i - 1)) (P.foot i s - toReal (P.vert i)) := by
      have hconst : cross (P.edgeDir (i - 1)) (toReal (P.vert i) - toReal (P.vert (i - 1))) = 0 := by
        rw [show toReal (P.vert i) - toReal (P.vert (i - 1)) = P.edgeDir (i - 1) from by
          rw [LatticePolygon.edgeDir, hi]]
        rw [cross]; ring
      have := (isLinearMap_cross (P.edgeDir (i - 1))).map_sub
        (P.foot i s - toReal (P.vert (i - 1))) (P.foot i s - toReal (P.vert i))
      rw [show (P.foot i s - toReal (P.vert (i - 1))) - (P.foot i s - toReal (P.vert i))
        = toReal (P.vert i) - toReal (P.vert (i - 1)) from by abel, hconst] at this
      linarith [this]
    have hfv : P.foot i s - toReal (P.vert i) = s • P.edgeDir i := by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
    have hcrosseq : cross (P.edgeDir (i - 1)) (P.foot i s - toReal (P.vert (i - 1)))
        = s * cross (P.edgeDir (i - 1)) (P.edgeDir i) := by
      rw [hvi, hfv]; exact (isLinearMap_cross (P.edgeDir (i - 1))).map_smul _ _
    have hbd := abs_cross_le_infDist P (i - 1) (P.foot i s)
    rw [hcrosseq, abs_mul, abs_of_nonneg hs0, ← hX] at hbd
    rw [div_mul_eq_mul_div, div_le_iff₀ hCdpos]
    calc X * s = s * X := by ring
      _ ≤ Cd * Metric.infDist (P.foot i s) (P.edgeSeg (i - 1)) := hbd
      _ = Metric.infDist (P.foot i s) (P.edgeSeg (i - 1)) * Cd := by ring

/-! ### Off-ray criteria near a vertex (for cap membership)

To place a near-vertex point `q` in `capA`/`capB` via `mem_capA_or_capB` we must know its
offset direction is *not* on either boundary ray. A short Euclidean-length argument: if
`q − v` were a nonnegative multiple of `−edgeDir i` (resp. `edgeDir (i+1)`) and small enough
(`eDist < edge length`), then `q` would lie on the incident edge, contradicting
off-boundary. -/

/-- `eDist` of a nonzero vector is positive. -/
lemma eDist_pos {v : ℝ × ℝ} (hv : v ≠ 0) : 0 < eDist v := by
  rcases lt_or_eq_of_le (eDist_nonneg v) with h | h
  · exact h
  · exfalso; apply hv
    have hz : v.1 ^ 2 + v.2 ^ 2 = 0 := by
      have := h.symm; rw [eDist, Real.sqrt_eq_zero (by positivity)] at this; exact this
    exact Prod.ext (show v.1 = 0 by nlinarith [sq_nonneg v.1, sq_nonneg v.2])
      (show v.2 = 0 by nlinarith [sq_nonneg v.1, sq_nonneg v.2])

/-- **Off the incoming ray (length form).** An off-boundary point `q` within Euclidean
distance `eDist (edgeDir i)` of the shared vertex `vert (i+1)` has `q − vert (i+1)` not a
nonnegative multiple of `−edgeDir i` (else `q` would lie on edge `i`). -/
lemma offRay_incoming_of_offBoundary (hsimple : P.IsSimple) (i : ZMod P.n) {q : ℝ × ℝ}
    (hqb : q ∉ P.boundary) (hlt : eDist (q - toReal (P.vert (i + 1))) < eDist (P.edgeDir i)) :
    ∀ c : ℝ, 0 ≤ c → q - toReal (P.vert (i + 1)) ≠ c • (-(P.edgeDir i)) := by
  intro c hc heq
  apply hqb
  rw [LatticePolygon.boundary, Set.mem_iUnion]
  refine ⟨i, ?_⟩
  have hcle : c < 1 := by
    have hee : eDist (q - toReal (P.vert (i + 1))) = c * eDist (P.edgeDir i) := by
      rw [heq, eDist_smul, abs_of_nonneg hc]; congr 1; rw [eDist, eDist]
      simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]
    rw [hee] at hlt
    have hed : 0 < eDist (P.edgeDir i) := eDist_pos (edgeDir_ne_zero P hsimple i)
    nlinarith [hlt, hed]
  rw [LatticePolygon.edgeSeg, segment_eq_image]
  refine ⟨1 - c, ⟨by linarith, by linarith⟩, ?_⟩
  have hq : q = toReal (P.vert (i + 1)) + c • (-(P.edgeDir i)) := by rw [← heq]; abel
  rw [hq, LatticePolygon.edgeDir]; module

/-- **Off the outgoing ray (length form).** An off-boundary point `q` within Euclidean
distance `eDist (edgeDir (i+1))` of the shared vertex `vert (i+1)` has `q − vert (i+1)` not a
nonnegative multiple of `edgeDir (i+1)` (else `q` would lie on edge `i+1`). -/
lemma offRay_outgoing_of_offBoundary (hsimple : P.IsSimple) (i : ZMod P.n) {q : ℝ × ℝ}
    (hqb : q ∉ P.boundary)
    (hlt : eDist (q - toReal (P.vert (i + 1))) < eDist (P.edgeDir (i + 1))) :
    ∀ c : ℝ, 0 ≤ c → q - toReal (P.vert (i + 1)) ≠ c • P.edgeDir (i + 1) := by
  intro c hc heq
  apply hqb
  rw [LatticePolygon.boundary, Set.mem_iUnion]
  refine ⟨i + 1, ?_⟩
  have hcle : c < 1 := by
    have hee : eDist (q - toReal (P.vert (i + 1))) = c * eDist (P.edgeDir (i + 1)) := by
      rw [heq, eDist_smul, abs_of_nonneg hc]
    rw [hee] at hlt
    have hed : 0 < eDist (P.edgeDir (i + 1)) := eDist_pos (edgeDir_ne_zero P hsimple (i + 1))
    nlinarith [hlt, hed]
  rw [LatticePolygon.edgeSeg, segment_eq_image]
  refine ⟨c, ⟨hc, by linarith⟩, ?_⟩
  have hq : q = toReal (P.vert (i + 1)) + c • P.edgeDir (i + 1) := by rw [← heq]; abel
  rw [hq, LatticePolygon.edgeDir]; module

/-- **Off-ray, incoming, as `Real.Angle`.** If `q − v` is never a nonnegative multiple of
`−edgeDir i`, its angle is `≢ α i` (mod 2π), since `α i = argOf (−edgeDir i)`. -/
lemma argOf_ne_alpha_of_offRay (hsimple : P.IsSimple) (i : ZMod P.n) {q : ℝ × ℝ}
    (hqne : q ≠ toReal (P.vert (i + 1)))
    (hray : ∀ c : ℝ, 0 ≤ c → q - toReal (P.vert (i + 1)) ≠ c • (-(P.edgeDir i))) :
    (↑(argOf (q - toReal (P.vert (i + 1)))) : Real.Angle) ≠ ↑(P.alpha i) := by
  intro hcontra
  set w := q - toReal (P.vert (i + 1)) with hw
  have hwne : w ≠ 0 := sub_ne_zero.mpr hqne
  have hepos : 0 < eDist w := eDist_pos hwne
  have hdne : (-(P.edgeDir i)) ≠ 0 := by rw [neg_ne_zero]; exact edgeDir_ne_zero P hsimple i
  have hd2 : 0 < eDist (-(P.edgeDir i)) := eDist_pos hdne
  have hdir : dirOf (argOf w) = dirOf (P.alpha i) := dirOf_eq_of_angle_eq hcontra
  rw [dirOf_argOf hwne, LatticePolygon.alpha, dirOf_argOf hdne] at hdir
  refine hray (eDist w * (eDist (-(P.edgeDir i)))⁻¹) (by positivity) ?_
  conv_lhs => rw [show w = eDist w • ((eDist w)⁻¹ • w) from by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hepos), one_smul], hdir]
  rw [smul_smul]

/-- **Off-ray, outgoing, as `Real.Angle`.** If `q − v` is never a nonnegative multiple of
`edgeDir (i+1)`, its angle is `≢ β i` (mod 2π), since `β i ≡ argOf (edgeDir (i+1))`. -/
lemma argOf_ne_beta_of_offRay (hsimple : P.IsSimple) (i : ZMod P.n) {q : ℝ × ℝ}
    (hqne : q ≠ toReal (P.vert (i + 1)))
    (hray : ∀ c : ℝ, 0 ≤ c → q - toReal (P.vert (i + 1)) ≠ c • P.edgeDir (i + 1)) :
    (↑(argOf (q - toReal (P.vert (i + 1)))) : Real.Angle) ≠ ↑(P.beta i) := by
  rw [beta_angle_eq]
  intro hcontra
  set w := q - toReal (P.vert (i + 1)) with hw
  have hwne : w ≠ 0 := sub_ne_zero.mpr hqne
  have hepos : 0 < eDist w := eDist_pos hwne
  have hdne : P.edgeDir (i + 1) ≠ 0 := edgeDir_ne_zero P hsimple (i + 1)
  have hd2 : 0 < eDist (P.edgeDir (i + 1)) := eDist_pos hdne
  have hdir : dirOf (argOf w) = dirOf (argOf (P.edgeDir (i + 1))) := dirOf_eq_of_angle_eq hcontra
  rw [dirOf_argOf hwne, dirOf_argOf hdne] at hdir
  refine hray (eDist w * (eDist (P.edgeDir (i + 1)))⁻¹) (by positivity) ?_
  conv_lhs => rw [show w = eDist w • ((eDist w)⁻¹ • w) from by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hepos), one_smul], hdir]
  rw [smul_smul]

/-! ### Assembling the tube cover

We now assemble the two-piece path-connected cover `L = (⋃ leftRegion) ∪ (⋃ capA)`,
`R = (⋃ rightRegion) ∪ (⋃ capB)` of the tube, and conclude `compl_boundary_atMost_two`. -/

/-- **The nearest boundary point lies on some edge with an interior or endpoint parameter.**
For `q ∉ boundary` and its nearest boundary point `p*` (`dist q p* = infDist q boundary`),
there is an edge index `i*` and `s ∈ [0,1]` with `p* = foot i* s` and `dist q (foot i* s)`
the boundary distance. -/
lemma exists_edge_foot_nearest (q : ℝ × ℝ) :
    ∃ (i : ZMod P.n) (s : ℝ), s ∈ Set.Icc (0:ℝ) 1 ∧
      dist q (P.foot i s) = Metric.infDist q P.boundary := by
  obtain ⟨p, hp, hnear⟩ := exists_nearest_boundary_point P q
  simp only [LatticePolygon.boundary, Set.mem_iUnion] at hp
  obtain ⟨i, hpi⟩ := hp
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hpi
  obtain ⟨s, hs, hps⟩ := hpi
  simp only at hps
  have hfoot : P.foot i s = p := by rw [LatticePolygon.foot, hps]
  exact ⟨i, s, hs, by rw [hfoot, hnear]⟩

/-- **Edge directions have Euclidean length `≥ 1`** (lattice endpoints: integer, nonzero
displacement). -/
lemma one_le_eDist_edgeDir (hsimple : P.IsSimple) (i : ZMod P.n) :
    (1:ℝ) ≤ eDist (P.edgeDir i) := by
  have h := edgeDir_ne_zero P hsimple i
  set a : ℤ := (P.vert (i+1)).1 - (P.vert i).1 with ha
  set b : ℤ := (P.vert (i+1)).2 - (P.vert i).2 with hb
  have hd : P.edgeDir i = ((a:ℝ), (b:ℝ)) := by
    simp only [LatticePolygon.edgeDir, toReal, ha, hb]
    push_cast; constructor
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc; rw [not_or] at hc; push Not at hc
    apply h; rw [hd, hc.1, hc.2]; simp
  rw [hd, eDist, show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  apply Real.sqrt_le_sqrt
  rcases hab with hne | hne
  · have h1 : (1:ℤ) ≤ a^2 := by nlinarith [Int.one_le_abs hne, sq_abs a]
    have h2 : (1:ℝ) ≤ (a:ℝ)^2 := by exact_mod_cast h1
    nlinarith [sq_nonneg (b:ℝ)]
  · have h1 : (1:ℤ) ≤ b^2 := by nlinarith [Int.one_le_abs hne, sq_abs b]
    have h2 : (1:ℝ) ≤ (b:ℝ)^2 := by exact_mod_cast h1
    nlinarith [sq_nonneg (a:ℝ)]

/-- **Distance between two feet on the same edge** equals `|s−s'|·‖edgeDir‖`. -/
lemma dist_foot_foot_eq (i : ZMod P.n) (s s' : ℝ) :
    dist (P.foot i s) (P.foot i s') = |s - s'| * ‖P.edgeDir i‖ := by
  have he : P.foot i s - P.foot i s' = (s - s') • P.edgeDir i := by
    rw [LatticePolygon.foot, LatticePolygon.foot, LatticePolygon.edgeDir]; module
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]

/-- **Distance between two feet on the same edge** is bounded by `|s−s'|·eDist (edgeDir)`. -/
lemma dist_foot_foot_le (i : ZMod P.n) (s s' : ℝ) :
    dist (P.foot i s) (P.foot i s') ≤ |s - s'| * eDist (P.edgeDir i) := by
  have he : P.foot i s - P.foot i s' = (s - s') • P.edgeDir i := by
    rw [LatticePolygon.foot, LatticePolygon.foot, LatticePolygon.edgeDir]; module
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_eDist _) (abs_nonneg _)

/-- **Edge-component bound (left).** The edge-parallel offset `|sE−s'|·eDist (edgeDir)` is
`≤` the Euclidean distance from `q = rectMap (leftNormal) (sE,t)` to `foot i s'`. -/
lemma eDist_edge_comp_le_left (i : ZMod P.n) {sE t s' : ℝ} {q : ℝ × ℝ}
    (hq : q = P.rectMap i (P.leftNormal i) (sE, t)) :
    |sE - s'| * eDist (P.edgeDir i) ≤ eDist (q - P.foot i s') := by
  have hsplit : q - P.foot i s' = t • P.leftNormal i + (sE - s') • P.edgeDir i := by
    rw [hq, LatticePolygon.rectMap, LatticePolygon.foot, LatticePolygon.edgeDir]; module
  have horth : (P.leftNormal i).1 * (P.edgeDir i).1 + (P.leftNormal i).2 * (P.edgeDir i).2 = 0 := by
    simp only [LatticePolygon.leftNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [← eDist_smul, eDist, eDist, hsplit]
  apply Real.sqrt_le_sqrt
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.add_def, smul_eq_mul]
  nlinarith [sq_nonneg (t * (P.leftNormal i).1), sq_nonneg (t * (P.leftNormal i).2),
    mul_eq_zero_of_right (2 * t * (sE - s')) horth]

/-- **Edge-component bound (right).** -/
lemma eDist_edge_comp_le_right (i : ZMod P.n) {sE t s' : ℝ} {q : ℝ × ℝ}
    (hq : q = P.rectMap i (P.rightNormal i) (sE, t)) :
    |sE - s'| * eDist (P.edgeDir i) ≤ eDist (q - P.foot i s') := by
  have hsplit : q - P.foot i s' = t • P.rightNormal i + (sE - s') • P.edgeDir i := by
    rw [hq, LatticePolygon.rectMap, LatticePolygon.foot, LatticePolygon.edgeDir]; module
  have horth : (P.rightNormal i).1 * (P.edgeDir i).1 + (P.rightNormal i).2 * (P.edgeDir i).2 = 0 := by
    simp only [LatticePolygon.rightNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [← eDist_smul, eDist, eDist, hsplit]
  apply Real.sqrt_le_sqrt
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.add_def, smul_eq_mul]
  nlinarith [sq_nonneg (t * (P.rightNormal i).1), sq_nonneg (t * (P.rightNormal i).2),
    mul_eq_zero_of_right (2 * t * (sE - s')) horth]

/-- **Region branch (left).** An off-boundary point `q` whose nearest boundary point is the
interior foot `foot i s` (`s ∈ (0,1)`, `dist q (foot i s) = δ > 0`), on the **left** of edge
`i` (`cross > 0`), and well-separated from every other edge (`3δ < infDist (foot i s) (edgeSeg j)`
for all `j ≠ i`), lands in `leftRegion i ε` whenever `√2·δ < ε`. -/
theorem mem_leftRegion_of_nearFoot (hsimple : P.IsSimple) (i : ZMod P.n) {s : ℝ}
    (hs : s ∈ Set.Ioo (0:ℝ) 1) {q : ℝ × ℝ} {δ ε : ℝ} (hδ : 0 < δ) (hδeq : dist q (P.foot i s) = δ)
    (hcross : 0 < cross (P.edgeDir i) (q - toReal (P.vert i)))
    (heps : Real.sqrt 2 * δ < ε)
    (hadj : ∀ j, j ≠ i → 3 * δ < Metric.infDist (P.foot i s) (P.edgeSeg j)) :
    q ∈ P.leftRegion i ε := by
  obtain ⟨s', t, hqeq, hcr⟩ := rectMap_left_coords P hsimple i q
  have hNpos : 0 < (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 := normSq_edgeDir_pos P hsimple i
  have hdnpos : 0 < ‖P.edgeDir i‖ := by rw [norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have htpos : 0 < t := by
    have hh : t * ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2) / ‖P.edgeDir i‖ > 0 := by
      rw [hcr]; exact hcross
    by_contra hc; push Not at hc
    exact absurd (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc hNpos.le)
      hdnpos.le) (by linarith)
  have hE : (1:ℝ) ≤ eDist (P.edgeDir i) := one_le_eDist_edgeDir P hsimple i
  have hcomp : |s' - s| * eDist (P.edgeDir i) ≤ eDist (q - P.foot i s) :=
    eDist_edge_comp_le_left P i hqeq
  have hed : eDist (q - P.foot i s) ≤ Real.sqrt 2 * δ := by rw [← hδeq]; exact eDist_sub_le_sqrt2_dist _ _
  have hcompδ : |s' - s| * eDist (P.edgeDir i) ≤ Real.sqrt 2 * δ := le_trans hcomp hed
  have hss' : |s' - s| ≤ Real.sqrt 2 * δ := by nlinarith [abs_nonneg (s' - s), hE, hcompδ]
  have hffle : dist (P.foot i s) (P.foot i s') ≤ Real.sqrt 2 * δ := by
    refine le_trans (dist_foot_foot_le P i s s') ?_
    rw [abs_sub_comm]; exact hcompδ
  have hsq2lt : Real.sqrt 2 < 3/2 := by
    rw [show (3/2:ℝ) = Real.sqrt ((3/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hi1 : i + 1 ≠ i := fun h => edgeDir_ne_zero P hsimple i (by rw [LatticePolygon.edgeDir, h]; simp)
  have him1 : i - 1 ≠ i := by
    intro h; apply hi1; have h2 : (i - 1) + 1 = i + 1 := by rw [h]
    rw [sub_add_cancel] at h2; exact h2.symm
  have hMpos : 0 < ‖P.edgeDir i‖ := hdnpos
  have hv1 : dist (P.foot i s) (toReal (P.vert (i+1))) = (1 - s) * ‖P.edgeDir i‖ := by
    rw [dist_eq_norm, show P.foot i s - toReal (P.vert (i+1)) = (1-s) • (-(P.edgeDir i)) from by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2]), norm_neg]
  have hv0 : dist (P.foot i s) (toReal (P.vert i)) = s * ‖P.edgeDir i‖ := by
    rw [dist_eq_norm, show P.foot i s - toReal (P.vert i) = s • (P.edgeDir i) from by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
  have hd1 : 3 * δ < (1 - s) * ‖P.edgeDir i‖ := by
    refine lt_of_lt_of_le (hadj (i+1) hi1) ?_
    rw [← hv1]
    exact Metric.infDist_le_dist_of_mem (by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _)
  have hd0 : 3 * δ < s * ‖P.edgeDir i‖ := by
    refine lt_of_lt_of_le (hadj (i-1) him1) ?_
    rw [← hv0]
    refine Metric.infDist_le_dist_of_mem ?_
    rw [LatticePolygon.edgeSeg, show toReal (P.vert i) = toReal (P.vert ((i-1)+1)) from by
      rw [sub_add_cancel]]
    exact right_mem_segment ℝ _ _
  have hMle : ‖P.edgeDir i‖ ≤ eDist (P.edgeDir i) := norm_le_eDist _
  have hss'M : |s' - s| * ‖P.edgeDir i‖ ≤ Real.sqrt 2 * δ :=
    le_trans (mul_le_mul_of_nonneg_left hMle (abs_nonneg _)) hcompδ
  have hs'Ioo : s' ∈ Set.Ioo (0:ℝ) 1 := by
    have hb : |s' - s| ≤ Real.sqrt 2 * δ / ‖P.edgeDir i‖ := by rw [le_div_iff₀ hMpos]; exact hss'M
    constructor
    · nlinarith [hd0, hMpos, hb, neg_abs_le (s'-s)]
    · nlinarith [hd1, hMpos, hb, le_abs_self (s'-s)]
  have htle : t ≤ Real.sqrt 2 * δ := by
    rw [← hδeq]; exact coord_le_sqrt2_dist_left P hsimple i htpos.le hqeq
  have htcap : t < P.capHeight i ε s' := by
    rw [LatticePolygon.capHeight, Finset.lt_inf'_iff]
    intro j _
    unfold LatticePolygon.capTerm
    by_cases hj : j = i
    · simp only [if_pos hj]; linarith [htle, heps]
    · simp only [if_neg hj]
      have htri : Metric.infDist (P.foot i s) (P.edgeSeg j)
          ≤ Metric.infDist (P.foot i s') (P.edgeSeg j) + dist (P.foot i s) (P.foot i s') :=
        Metric.infDist_le_infDist_add_dist
      have hadjj := hadj j hj
      nlinarith [htle, hffle, htri, hadjj, hsq2lt, hδ]
  exact ⟨(s', t), ⟨hs'Ioo, htpos, htcap⟩, hqeq.symm⟩

/-- **Region branch (right).** Mirror of `mem_leftRegion_of_nearFoot` for `cross < 0`. -/
theorem mem_rightRegion_of_nearFoot (hsimple : P.IsSimple) (i : ZMod P.n) {s : ℝ}
    (hs : s ∈ Set.Ioo (0:ℝ) 1) {q : ℝ × ℝ} {δ ε : ℝ} (hδ : 0 < δ) (hδeq : dist q (P.foot i s) = δ)
    (hcross : cross (P.edgeDir i) (q - toReal (P.vert i)) < 0)
    (heps : Real.sqrt 2 * δ < ε)
    (hadj : ∀ j, j ≠ i → 3 * δ < Metric.infDist (P.foot i s) (P.edgeSeg j)) :
    q ∈ P.rightRegion i ε := by
  set s' : ℝ := ((q - toReal (P.vert i)).1 * (P.edgeDir i).1
      + (q - toReal (P.vert i)).2 * (P.edgeDir i).2)
      / ((P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2) with hs'def
  obtain ⟨t, htpos, hqeq⟩ := exists_mem_rightRect_of_cross_neg P hsimple i hcross hs'def
  have hdnpos : 0 < ‖P.edgeDir i‖ := by rw [norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have hE : (1:ℝ) ≤ eDist (P.edgeDir i) := one_le_eDist_edgeDir P hsimple i
  have hcomp : |s' - s| * eDist (P.edgeDir i) ≤ eDist (q - P.foot i s) :=
    eDist_edge_comp_le_right P i hqeq
  have hed : eDist (q - P.foot i s) ≤ Real.sqrt 2 * δ := by rw [← hδeq]; exact eDist_sub_le_sqrt2_dist _ _
  have hcompδ : |s' - s| * eDist (P.edgeDir i) ≤ Real.sqrt 2 * δ := le_trans hcomp hed
  have hffle : dist (P.foot i s) (P.foot i s') ≤ Real.sqrt 2 * δ := by
    refine le_trans (dist_foot_foot_le P i s s') ?_
    rw [abs_sub_comm]; exact hcompδ
  have hsq2lt : Real.sqrt 2 < 3/2 := by
    rw [show (3/2:ℝ) = Real.sqrt ((3/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hi1 : i + 1 ≠ i := fun h => edgeDir_ne_zero P hsimple i (by rw [LatticePolygon.edgeDir, h]; simp)
  have him1 : i - 1 ≠ i := by
    intro h; apply hi1; have h2 : (i - 1) + 1 = i + 1 := by rw [h]
    rw [sub_add_cancel] at h2; exact h2.symm
  have hMpos : 0 < ‖P.edgeDir i‖ := hdnpos
  have hv1 : dist (P.foot i s) (toReal (P.vert (i+1))) = (1 - s) * ‖P.edgeDir i‖ := by
    rw [dist_eq_norm, show P.foot i s - toReal (P.vert (i+1)) = (1-s) • (-(P.edgeDir i)) from by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2]), norm_neg]
  have hv0 : dist (P.foot i s) (toReal (P.vert i)) = s * ‖P.edgeDir i‖ := by
    rw [dist_eq_norm, show P.foot i s - toReal (P.vert i) = s • (P.edgeDir i) from by
      rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
  have hd1 : 3 * δ < (1 - s) * ‖P.edgeDir i‖ := by
    refine lt_of_lt_of_le (hadj (i+1) hi1) ?_
    rw [← hv1]
    exact Metric.infDist_le_dist_of_mem (by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _)
  have hd0 : 3 * δ < s * ‖P.edgeDir i‖ := by
    refine lt_of_lt_of_le (hadj (i-1) him1) ?_
    rw [← hv0]
    refine Metric.infDist_le_dist_of_mem ?_
    rw [LatticePolygon.edgeSeg, show toReal (P.vert i) = toReal (P.vert ((i-1)+1)) from by
      rw [sub_add_cancel]]
    exact right_mem_segment ℝ _ _
  have hMle : ‖P.edgeDir i‖ ≤ eDist (P.edgeDir i) := norm_le_eDist _
  have hss'M : |s' - s| * ‖P.edgeDir i‖ ≤ Real.sqrt 2 * δ :=
    le_trans (mul_le_mul_of_nonneg_left hMle (abs_nonneg _)) hcompδ
  have hs'Ioo : s' ∈ Set.Ioo (0:ℝ) 1 := by
    have hb : |s' - s| ≤ Real.sqrt 2 * δ / ‖P.edgeDir i‖ := by rw [le_div_iff₀ hMpos]; exact hss'M
    constructor
    · nlinarith [hd0, hMpos, hb, neg_abs_le (s'-s)]
    · nlinarith [hd1, hMpos, hb, le_abs_self (s'-s)]
  have htle : t ≤ Real.sqrt 2 * δ := by
    rw [← hδeq]; exact coord_le_sqrt2_dist_right P hsimple i htpos.le hqeq
  have htcap : t < P.capHeight i ε s' := by
    rw [LatticePolygon.capHeight, Finset.lt_inf'_iff]
    intro j _
    unfold LatticePolygon.capTerm
    by_cases hj : j = i
    · simp only [if_pos hj]; linarith [htle, heps]
    · simp only [if_neg hj]
      have htri : Metric.infDist (P.foot i s) (P.edgeSeg j)
          ≤ Metric.infDist (P.foot i s') (P.edgeSeg j) + dist (P.foot i s) (P.foot i s') :=
        Metric.infDist_le_infDist_add_dist
      have hadjj := hadj j hj
      nlinarith [htle, hffle, htri, hadjj, hsq2lt, hδ]
  exact ⟨(s', t), ⟨hs'Ioo, htpos, htcap⟩, hqeq.symm⟩

/-- **Euclidean-length triangle inequality.** -/
theorem eDist_add_le (u v : ℝ × ℝ) : eDist (u + v) ≤ eDist u + eDist v := by
  have hab : u.1*v.1 + u.2*v.2 ≤ Real.sqrt (u.1^2+u.2^2) * Real.sqrt (v.1^2+v.2^2) := by
    rw [← Real.sqrt_mul (by positivity)]
    rcases le_or_gt (u.1*v.1+u.2*v.2) 0 with h | h
    · exact le_trans h (Real.sqrt_nonneg _)
    · rw [Real.le_sqrt (le_of_lt h) (by positivity)]; nlinarith [sq_nonneg (u.1*v.2 - u.2*v.1)]
  simp only [eDist, Prod.fst_add, Prod.snd_add]
  rw [show Real.sqrt (u.1^2+u.2^2) + Real.sqrt (v.1^2+v.2^2)
      = |Real.sqrt (u.1^2+u.2^2) + Real.sqrt (v.1^2+v.2^2)| from (abs_of_nonneg (by positivity)).symm,
    ← Real.sqrt_sq (abs_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [sq_abs]
  nlinarith [hab, Real.sq_sqrt (show (0:ℝ) ≤ u.1^2+u.2^2 by positivity),
    Real.sq_sqrt (show (0:ℝ) ≤ v.1^2+v.2^2 by positivity),
    Real.sqrt_nonneg (u.1^2+u.2^2), Real.sqrt_nonneg (v.1^2+v.2^2)]

/-- **Cap branch.** An off-boundary point `q` near the vertex `vert (i+1)`, within Euclidean
distance `< eDist (edgeDir i)`, `< eDist (edgeDir (i+1))` and `< capR`, lands in `capA i capR`
or `capB i capR`. -/
theorem mem_capA_or_capB_of_near_vertex (hsimple : P.IsSimple) (i : ZMod P.n) {capR : ℝ}
    {q : ℝ × ℝ} (hqb : q ∉ P.boundary) (hqne : q ≠ toReal (P.vert (i+1)))
    (hin : eDist (q - toReal (P.vert (i+1))) < eDist (P.edgeDir i))
    (hout : eDist (q - toReal (P.vert (i+1))) < eDist (P.edgeDir (i+1)))
    (hball : eDist (q - toReal (P.vert (i + 1))) < capR) :
    q ∈ P.capA i capR ∨ q ∈ P.capB i capR := by
  have hray_in := offRay_incoming_of_offBoundary P hsimple i hqb hin
  have hray_out := offRay_outgoing_of_offBoundary P hsimple i hqb hout
  exact mem_capA_or_capB P i hqne (argOf_ne_alpha_of_offRay P hsimple i hqne hray_in)
    (argOf_ne_beta_of_offRay P hsimple i hqne hray_out) hball

/-- **Off-line case is impossible for an interior nearest foot.** If `foot i s` (`s ∈ (0,1)`)
is the nearest point of edge `i` to an off-boundary `q`, then `cross (edgeDir i) (q − vert i) ≠ 0`:
a zero cross would place `q` on the edge line at some parameter `s''`, and the nearest-point
property (compared at the two endpoints) forces `s'' ∈ [0,1]`, i.e. `q ∈ edgeSeg i`,
contradicting off-boundary. -/
theorem cross_ne_zero_of_interior_nearest (hsimple : P.IsSimple) (i : ZMod P.n) {q : ℝ×ℝ} {s : ℝ}
    (hqb : q ∉ P.boundary)
    (hsegeq : Metric.infDist q (P.edgeSeg i) = dist q (P.foot i s)) (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    cross (P.edgeDir i) (q - toReal (P.vert i)) ≠ 0 := by
  intro heq
  obtain ⟨s'', t, hqeq, hcr⟩ := rectMap_left_coords P hsimple i q
  have hNpos : 0 < (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 := normSq_edgeDir_pos P hsimple i
  have hdnpos : 0 < ‖P.edgeDir i‖ := by rw [norm_pos_iff]; exact edgeDir_ne_zero P hsimple i
  have ht0 : t = 0 := by
    rw [heq] at hcr; rw [div_eq_zero_iff] at hcr
    rcases hcr with h | h
    · rcases mul_eq_zero.mp h with h2 | h2
      · exact h2
      · exact absurd h2 (by positivity)
    · exact absurd h (by positivity)
  have hqfoot : q = P.foot i s'' := by rw [hqeq, ht0, LatticePolygon.rectMap, LatticePolygon.foot]; simp
  set M := ‖P.edgeDir i‖ with hM
  have hdistgen : ∀ σ : ℝ, dist q (P.foot i σ) = |s'' - σ| * M := by
    intro σ; rw [hqfoot, dist_foot_foot_eq]
  have hle0 : dist q (P.foot i s) ≤ dist q (P.foot i 0) := by
    rw [← hsegeq]; exact Metric.infDist_le_dist_of_mem
      (by rw [LatticePolygon.edgeSeg, LatticePolygon.foot]; simp; exact left_mem_segment ℝ _ _)
  have hle1 : dist q (P.foot i s) ≤ dist q (P.foot i 1) := by
    rw [← hsegeq]; exact Metric.infDist_le_dist_of_mem
      (by rw [LatticePolygon.edgeSeg, LatticePolygon.foot]; simp; exact right_mem_segment ℝ _ _)
  rw [hdistgen s, hdistgen 0] at hle0
  rw [hdistgen s, hdistgen 1] at hle1
  have h0 : |s'' - s| ≤ |s'' - 0| := by nlinarith [hle0, hdnpos, abs_nonneg (s''-s), abs_nonneg (s''-0)]
  have h1 : |s'' - s| ≤ |s'' - 1| := by nlinarith [hle1, hdnpos, abs_nonneg (s''-s), abs_nonneg (s''-1)]
  have hs''mem : s'' ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · by_contra hc; push Not at hc
      rw [sub_zero, abs_of_neg hc, abs_of_neg (by linarith [hs.1] : s'' - s < 0)] at h0
      linarith [hs.1]
    · by_contra hc; push Not at hc
      rw [abs_of_pos (by linarith : s'' - 1 > 0), abs_of_pos (by linarith [hs.2] : s'' - s > 0)] at h1
      linarith [hs.2]
  apply hqb
  rw [hqfoot, LatticePolygon.boundary, Set.mem_iUnion]
  refine ⟨i, ?_⟩
  rw [LatticePolygon.edgeSeg, LatticePolygon.foot]
  exact ⟨1 - s'', s'', by linarith [hs''mem.2], hs''mem.1, by ring, rfl⟩

/-- **Tube cover membership (abstract constants).** Under the constant conditions, every tube
point lies in one of the four cover pieces: a left region, a right region, a left cap (`capA`),
or a right cap (`capB`). -/
theorem tube_cover_mem (hsimple : P.IsSimple) {εt εreg capR r Cmax : ℝ}
    (_ : 0 < r)
    (hrclear : ∀ i j : ZMod P.n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      ∀ x ∈ P.edgeSeg i, ∀ x' ∈ P.edgeSeg j, r ≤ dist x x')
    (h3r : 3 * εt < r)
    (hsqreg : Real.sqrt 2 * εt < εreg)
    (hCmax_nn : 0 ≤ Cmax)
    (hCs : ∀ i : ZMod P.n, ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ ρ : ℝ,
      Metric.infDist (P.foot i s) (P.edgeSeg (i+1)) ≤ ρ →
      eDist (P.foot i s - toReal (P.vert (i+1))) ≤ Cmax * ρ)
    (hCp : ∀ i : ZMod P.n, ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ ρ : ℝ,
      Metric.infDist (P.foot i s) (P.edgeSeg (i-1)) ≤ ρ →
      eDist (P.foot i s - toReal (P.vert i)) ≤ Cmax * ρ)
    (hcapbnd : Real.sqrt 2 * εt + Cmax * (3 * εt) < capR)
    (hcapR1 : capR ≤ 1)
    {q : ℝ × ℝ} (hq : q ∈ P.Tube εt) :
    (∃ i, q ∈ P.leftRegion i εreg) ∨ (∃ i, q ∈ P.capB i capR) ∨
      (∃ i, q ∈ P.rightRegion i εreg) ∨ (∃ i, q ∈ P.capA i capR) := by
  rw [mem_Tube_iff] at hq
  obtain ⟨hpos, hlt⟩ := hq
  have hqb : q ∉ P.boundary := by
    rw [(boundary_isClosed P).notMem_iff_infDist_pos (boundary_nonempty P)]; exact hpos
  have hεt : 0 < εt := lt_of_le_of_lt (le_of_lt hpos) hlt
  -- cap-near-vertex helper
  have capvert : ∀ k : ZMod P.n, eDist (q - toReal (P.vert (k+1))) < capR →
      (∃ i, q ∈ P.capB i capR) ∨ (∃ i, q ∈ P.capA i capR) := by
    intro k hkv
    have hvb : toReal (P.vert (k+1)) ∈ P.boundary := by
      rw [LatticePolygon.boundary, Set.mem_iUnion]
      exact ⟨k, by rw [LatticePolygon.edgeSeg]
                   exact right_mem_segment ℝ (toReal (P.vert k)) (toReal (P.vert (k+1)))⟩
    have hqne : q ≠ toReal (P.vert (k+1)) := fun h => hqb (h ▸ hvb)
    have hin : eDist (q - toReal (P.vert (k+1))) < eDist (P.edgeDir k) :=
      lt_of_lt_of_le hkv (le_trans hcapR1 (one_le_eDist_edgeDir P hsimple k))
    have hout : eDist (q - toReal (P.vert (k+1))) < eDist (P.edgeDir (k+1)) :=
      lt_of_lt_of_le hkv (le_trans hcapR1 (one_le_eDist_edgeDir P hsimple (k+1)))
    rcases mem_capA_or_capB_of_near_vertex P hsimple k hqb hqne hin hout hkv with hA | hB
    · exact Or.inr ⟨k, hA⟩
    · exact Or.inl ⟨k, hB⟩
  obtain ⟨i, s, hsIcc, hfeq⟩ := exists_edge_foot_nearest P q
  set δ := dist q (P.foot i s) with hδdef
  have hδlt : δ < εt := by rw [hfeq]; exact hlt
  have hδpos : 0 < δ := by rw [hfeq]; exact hpos
  have hqfoot_eDist : eDist (q - P.foot i s) ≤ Real.sqrt 2 * δ := by
    rw [hδdef]; exact eDist_sub_le_sqrt2_dist _ _
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- cap from a vertex achieved by foot when eDist(q-vert) < capR via foot bound
  -- VERTEX CASE: s = 0 or s = 1
  rcases eq_or_lt_of_le hsIcc.1 with hs0 | hs0pos
  · -- s = 0: foot i 0 = vert i = vert((i-1)+1)
    have hfoot0 : P.foot i s = toReal (P.vert i) := by
      rw [← hs0, LatticePolygon.foot]; simp
    have hkv : eDist (q - toReal (P.vert ((i-1)+1))) < capR := by
      rw [show (i-1)+1 = i from by rw [sub_add_cancel], ← hfoot0]
      calc eDist (q - P.foot i s) ≤ Real.sqrt 2 * δ := hqfoot_eDist
        _ < Real.sqrt 2 * εt := by nlinarith [hsqrt2pos, hδlt]
        _ ≤ capR := by nlinarith [hCmax_nn, hεt, hcapbnd]
    rcases capvert (i-1) hkv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  rcases eq_or_lt_of_le hsIcc.2 with hs1 | hs1lt
  · -- s = 1: foot i 1 = vert (i+1)
    have hfoot1 : P.foot i s = toReal (P.vert (i+1)) := by
      rw [hs1, LatticePolygon.foot]; simp
    have hkv : eDist (q - toReal (P.vert (i+1))) < capR := by
      rw [← hfoot1]
      calc eDist (q - P.foot i s) ≤ Real.sqrt 2 * δ := hqfoot_eDist
        _ < Real.sqrt 2 * εt := by nlinarith [hsqrt2pos, hδlt]
        _ ≤ capR := by nlinarith [hCmax_nn, hεt, hcapbnd]
    rcases capvert i hkv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  -- INTERIOR CASE: s ∈ (0,1)
  have hsIoo : s ∈ Set.Ioo (0:ℝ) 1 := ⟨hs0pos, hs1lt⟩
  -- infDist q (edgeSeg i) = δ
  have hsegeq : Metric.infDist q (P.edgeSeg i) = δ := by
    refine le_antisymm ?_ ?_
    · exact Metric.infDist_le_dist_of_mem (foot_mem_edgeSeg P i hsIoo)
    · rw [hfeq]
      exact Metric.infDist_le_infDist_of_subset
        (by rw [LatticePolygon.boundary]; exact Set.subset_iUnion _ i)
        ⟨toReal (P.vert i), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩
  -- adjacency indices
  have hi1 : i + 1 ≠ i := fun h => edgeDir_ne_zero P hsimple i (by rw [LatticePolygon.edgeDir, h]; simp)
  have him1 : i - 1 ≠ i := by
    intro h; apply hi1; have h2 : (i - 1) + 1 = i + 1 := by rw [h]
    rw [sub_add_cancel] at h2; exact h2.symm
  -- clearance: for j ∉ {i, i+1, i-1}, infDist (foot i s) (edgeSeg j) ≥ r > 3δ
  have hclear : ∀ j, j ≠ i → j ≠ i+1 → j ≠ i-1 → 3 * δ < Metric.infDist (P.foot i s) (P.edgeSeg j) := by
    intro j hji hji1 hjim1
    have hjp1i : j + 1 ≠ i := by
      intro h; apply hjim1; rw [← h]; ring
    have hrle : r ≤ Metric.infDist (P.foot i s) (P.edgeSeg j) := by
      rw [Metric.le_infDist ⟨toReal (P.vert j), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩]
      intro y hy
      exact hrclear i j (Ne.symm hji) (Ne.symm hji1) hjp1i (P.foot i s) (foot_mem_edgeSeg P i hsIoo) y hy
    linarith [h3r, hδlt, hrle]
  -- dichotomy on the two adjacent edges
  by_cases hsucc : Metric.infDist (P.foot i s) (P.edgeSeg (i+1)) ≤ 3 * εt
  · -- cap via successor edge
    have hbnd := hCs i s hsIoo (3 * εt) hsucc
    have hkv : eDist (q - toReal (P.vert (i+1))) < capR := by
      have htri : eDist (q - toReal (P.vert (i+1)))
          ≤ eDist (q - P.foot i s) + eDist (P.foot i s - toReal (P.vert (i+1))) := by
        rw [show q - toReal (P.vert (i+1)) = (q - P.foot i s) + (P.foot i s - toReal (P.vert (i+1))) from by abel]
        exact eDist_add_le _ _
      calc eDist (q - toReal (P.vert (i+1)))
          ≤ eDist (q - P.foot i s) + eDist (P.foot i s - toReal (P.vert (i+1))) := htri
        _ ≤ Real.sqrt 2 * δ + Cmax * (3 * εt) := by
            apply add_le_add hqfoot_eDist hbnd
        _ < Real.sqrt 2 * εt + Cmax * (3 * εt) := by nlinarith [hsqrt2pos, hδlt]
        _ < capR := hcapbnd
    rcases capvert i hkv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  by_cases hpred : Metric.infDist (P.foot i s) (P.edgeSeg (i-1)) ≤ 3 * εt
  · -- cap via predecessor edge: vertex vert i
    have hbnd := hCp i s hsIoo (3 * εt) hpred
    have hkv : eDist (q - toReal (P.vert ((i-1)+1))) < capR := by
      rw [show (i-1)+1 = i from by rw [sub_add_cancel]]
      have htri : eDist (q - toReal (P.vert i))
          ≤ eDist (q - P.foot i s) + eDist (P.foot i s - toReal (P.vert i)) := by
        rw [show q - toReal (P.vert i) = (q - P.foot i s) + (P.foot i s - toReal (P.vert i)) from by abel]
        exact eDist_add_le _ _
      calc eDist (q - toReal (P.vert i))
          ≤ eDist (q - P.foot i s) + eDist (P.foot i s - toReal (P.vert i)) := htri
        _ ≤ Real.sqrt 2 * δ + Cmax * (3 * εt) := by apply add_le_add hqfoot_eDist hbnd
        _ < Real.sqrt 2 * εt + Cmax * (3 * εt) := by nlinarith [hsqrt2pos, hδlt]
        _ < capR := hcapbnd
    rcases capvert (i-1) hkv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  -- REGION branch: both adjacent infDists > 3εt > 3δ
  push Not at hsucc hpred
  have hadj : ∀ j, j ≠ i → 3 * δ < Metric.infDist (P.foot i s) (P.edgeSeg j) := by
    intro j hji
    by_cases hj1 : j = i + 1
    · subst hj1; linarith [hsucc, h3r, hδlt, hεt]
    by_cases hjm1 : j = i - 1
    · subst hjm1; linarith [hpred, h3r, hδlt, hεt]
    · exact hclear j hji hj1 hjm1
  -- cross sign dichotomy
  have hcrne := cross_ne_zero_of_interior_nearest P hsimple i hqb hsegeq hsIoo
  rcases lt_trichotomy (cross (P.edgeDir i) (q - toReal (P.vert i))) 0 with hcr | hcr | hcr
  · -- right region
    have hheps : Real.sqrt 2 * δ < εreg := by nlinarith [hsqrt2pos, hδlt, hsqreg]
    exact Or.inr (Or.inr (Or.inl ⟨i, mem_rightRegion_of_nearFoot P hsimple i hsIoo hδpos hδdef.symm hcr hheps hadj⟩))
  · exact absurd hcr hcrne
  · -- left region
    have hheps : Real.sqrt 2 * δ < εreg := by nlinarith [hsqrt2pos, hδlt, hsqreg]
    exact Or.inl ⟨i, mem_leftRegion_of_nearFoot P hsimple i hsIoo hδpos hδdef.symm hcr hheps hadj⟩

/-! ### Assembly: path-connectivity of the two cover halves from the meet families

Each half (`L = ⋃ leftRegion ∪ ⋃ capB`, `R = ⋃ rightRegion ∪ ⋃ capA`) is the union of a
`ZMod n ⊕ ZMod n`-indexed family of path-connected pieces. The "meet" relation links
`inl i — inr i` (region meets its corner cap) and `inr i — inl (i+1)` (cap meets the next
region), which forms one cycle through all indices; `isPathConnected_iUnion_of_reflTransGen`
then makes the union path-connected. -/

/-- **Cyclic reach.** For `f : ZMod n → β` and a relation `rel` on `β` with
`ReflTransGen rel (f i) (f (i+1))` for every `i`, we have `ReflTransGen rel (f i) (f (i + m))`
for every `m : ℕ`. -/
lemma reflTransGen_zmod_succ {β : Type*} {rel : β → β → Prop} {f : ZMod P.n → β}
    (hstep : ∀ i, Relation.ReflTransGen rel (f i) (f (i + 1))) (i : ZMod P.n) (m : ℕ) :
    Relation.ReflTransGen rel (f i) (f (i + (m : ZMod P.n))) := by
  induction m with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ k ih =>
    refine ih.trans ?_
    have he : i + ((k : ZMod P.n) + 1) = (i + (k : ZMod P.n)) + 1 := by ring
    rw [Nat.cast_succ, he]
    exact hstep _

/-- **Total cyclic reach.** With the cyclic step `ReflTransGen rel (f i) (f (i+1))` for all `i`,
`ReflTransGen rel (f i) (f j)` holds for every `i, j`. -/
lemma reflTransGen_zmod_total {β : Type*} {rel : β → β → Prop} {f : ZMod P.n → β}
    (hstep : ∀ i, Relation.ReflTransGen rel (f i) (f (i + 1))) (i j : ZMod P.n) :
    Relation.ReflTransGen rel (f i) (f j) := by
  have h := reflTransGen_zmod_succ P hstep i (j - i).val
  rwa [ZMod.natCast_val, ZMod.cast_id, add_sub_cancel] at h

/-- **Path-connected two-family cycle.** Given two `ZMod n`-indexed families `g i` (regions)
and `c i` (caps), each path-connected, with the cyclic meets `g i ∩ c i` and `c i ∩ g (i+1)`
nonempty, the union `(⋃ g) ∪ (⋃ c)` is path-connected. -/
lemma isPathConnected_region_cap_cycle
    {g c : ZMod P.n → Set (ℝ × ℝ)}
    (hg : ∀ i, IsPathConnected (g i)) (hc : ∀ i, IsPathConnected (c i))
    (hgc : ∀ i, (g i ∩ c i).Nonempty) (hcg : ∀ i, (c i ∩ g (i + 1)).Nonempty) :
    IsPathConnected ((⋃ i, g i) ∪ (⋃ i, c i)) := by
  -- the combined family over the index `ZMod n ⊕ ZMod n`
  set F : ZMod P.n ⊕ ZMod P.n → Set (ℝ × ℝ) := fun x => Sum.elim g c x with hF
  have hunion : (⋃ x, F x) = (⋃ i, g i) ∪ (⋃ i, c i) := by
    rw [Set.iUnion_sum]; rfl
  rw [← hunion]
  apply isPathConnected_iUnion_of_reflTransGen
  · rintro (i | i) <;> simp only [hF, Sum.elim_inl, Sum.elim_inr]
    · exact hg i
    · exact hc i
  · -- meet relation on the sum index
    set rel : ZMod P.n ⊕ ZMod P.n → ZMod P.n ⊕ ZMod P.n → Prop :=
      fun x y => (F x ∩ F y).Nonempty with hrel
    -- the per-step relation on ZMod n: inl i reaches inl (i+1)
    have hstep : ∀ i : ZMod P.n,
        Relation.ReflTransGen rel (Sum.inl i) (Sum.inl (i + 1)) := by
      intro i
      have h1 : rel (Sum.inl i) (Sum.inr i) := by
        simpa only [hrel, hF, Sum.elim_inl, Sum.elim_inr] using hgc i
      have h2 : rel (Sum.inr i) (Sum.inl (i + 1)) := by
        simpa only [hrel, hF, Sum.elim_inl, Sum.elim_inr] using hcg i
      exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.single h2)
    -- inl i reaches inl j for all i, j
    have hll : ∀ i j : ZMod P.n, Relation.ReflTransGen rel (Sum.inl i) (Sum.inl j) :=
      reflTransGen_zmod_total P (f := Sum.inl) hstep
    -- inl i reaches inr j: go inl i → inl j → inr j
    have hlr : ∀ i j : ZMod P.n, Relation.ReflTransGen rel (Sum.inl i) (Sum.inr j) := by
      intro i j
      refine (hll i j).tail ?_
      simpa only [hrel, hF, Sum.elim_inl, Sum.elim_inr] using hgc j
    -- now connect any two sum-indices via inl 0
    rintro (i | i) (j | j)
    · exact hll i j
    · exact hlr i j
    · -- inr i → inl i → inl j  : use symmetry of the meet relation
      refine Relation.ReflTransGen.head ?_ (hll i j)
      simpa only [hrel, hF, Sum.elim_inl, Sum.elim_inr, Set.inter_comm] using hgc i
    · -- inr i → inl i → inr j
      refine Relation.ReflTransGen.head ?_ (hlr i j)
      simpa only [hrel, hF, Sum.elim_inl, Sum.elim_inr, Set.inter_comm] using hgc i

/-- **Concrete tube cover.** There exist `εt > 0` and `εreg, capR > 0` with `capR ≤ featureSize`,
such that the tube `Tube εt` is covered by the four families of pieces, all off-boundary. -/
theorem exists_tube_cover (hsimple : P.IsSimple) :
    ∃ εt εreg capR : ℝ, 0 < εt ∧ 0 < εreg ∧ 0 < capR ∧ capR ≤ P.featureSize ∧
      P.Tube εt ⊆ ((⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR)) ∪
                  ((⋃ i, P.rightRegion i εreg) ∪ (⋃ i, P.capA i capR)) := by
  classical
  obtain ⟨r, hr, hrclear⟩ := edgeClearance_pos P hsimple
  set Cs : ZMod P.n → ℝ := fun i => (foot_near_succ_edge_near_vertex P hsimple i).choose with hCsdef
  set Cp : ZMod P.n → ℝ := fun i => (foot_near_pred_edge_near_vertex P hsimple i).choose with hCpdef
  set Cmax : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := ZMod P.n))
    (fun i => max (Cs i) (Cp i)) with hCmaxdef
  have hsup : ∀ i, max (Cs i) (Cp i) ≤ Cmax :=
    fun i => Finset.le_sup' (fun i => max (Cs i) (Cp i)) (Finset.mem_univ i)
  have hCmax_s : ∀ i, Cs i ≤ Cmax := fun i => le_trans (le_max_left _ _) (hsup i)
  have hCmax_p : ∀ i, Cp i ≤ Cmax := fun i => le_trans (le_max_right _ _) (hsup i)
  have hCmax_nn : 0 ≤ Cmax :=
    le_trans (le_of_lt (foot_near_succ_edge_near_vertex P hsimple 0).choose_spec.1) (hCmax_s 0)
  have hfs : 0 < P.featureSize := featureSize_pos P hsimple
  set B : ℝ := min (min P.featureSize 1) r with hBdef
  have hBpos : 0 < B := by rw [hBdef]; exact lt_min (lt_min hfs one_pos) hr
  have hBle : B ≤ min P.featureSize 1 := min_le_left _ _
  have hBr : B ≤ r := min_le_right _ _
  have hden : 0 < 16 * (Cmax + 1) := by positivity
  set εt : ℝ := B / (16 * (Cmax + 1)) with hεtdef
  have hεtpos : 0 < εt := by rw [hεtdef]; positivity
  set capR : ℝ := min P.featureSize 1 / 2 with hcapRdef
  have hcapRpos : 0 < capR := by rw [hcapRdef]; exact div_pos (lt_min hfs one_pos) (by norm_num)
  have hcapR1 : capR ≤ 1 := by rw [hcapRdef]; have := min_le_right P.featureSize 1; linarith
  have hcapRfs : capR ≤ P.featureSize := by rw [hcapRdef]; have := min_le_left P.featureSize 1; linarith
  have hsqrt2lt : Real.sqrt 2 < 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 from by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsqrt2nn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h3r : 3 * εt < r := by
    rw [hεtdef]
    have h1 : B / (16 * (Cmax + 1)) ≤ B / 16 :=
      div_le_div_of_nonneg_left hBpos.le (by norm_num) (by nlinarith [hCmax_nn])
    nlinarith [h1, hBr, hBpos]
  have hsqreg : Real.sqrt 2 * εt < 2 * εt := by nlinarith [hεtpos, hsqrt2lt]
  have hcapbnd : Real.sqrt 2 * εt + Cmax * (3 * εt) < capR := by
    rw [hεtdef, hcapRdef]
    set εt' := B / (16 * (Cmax + 1)) with hε
    have hεval : εt' * (16 * (Cmax + 1)) = B := by rw [hε]; field_simp
    have hεpos : 0 < εt' := by rw [hε]; positivity
    have hkey : Real.sqrt 2 * εt' + Cmax * (3 * εt') ≤ εt' * (4 * (Cmax + 1)) := by
      nlinarith [hεpos, hCmax_nn, hsqrt2lt]
    have h4 : εt' * (4 * (Cmax + 1)) = B / 4 := by rw [hε]; field_simp; ring
    rw [h4] at hkey
    have : B / 4 < min P.featureSize 1 / 2 := by nlinarith [hBle, hBpos]
    linarith
  -- the cap constants for tube_cover_mem
  have hCs : ∀ i : ZMod P.n, ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ ρ : ℝ,
      Metric.infDist (P.foot i s) (P.edgeSeg (i+1)) ≤ ρ →
      eDist (P.foot i s - toReal (P.vert (i+1))) ≤ Cmax * ρ := by
    intro i s hs ρ hρ
    have hspec := (foot_near_succ_edge_near_vertex P hsimple i).choose_spec.2 s hs ρ hρ
    rcases le_or_gt 0 ρ with hρ0 | hρ0
    · exact le_trans hspec (mul_le_mul_of_nonneg_right (hCmax_s i) hρ0)
    · exfalso; exact absurd (le_trans Metric.infDist_nonneg hρ) (by linarith)
  have hCp : ∀ i : ZMod P.n, ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ ρ : ℝ,
      Metric.infDist (P.foot i s) (P.edgeSeg (i-1)) ≤ ρ →
      eDist (P.foot i s - toReal (P.vert i)) ≤ Cmax * ρ := by
    intro i s hs ρ hρ
    have hspec := (foot_near_pred_edge_near_vertex P hsimple i).choose_spec.2 s hs ρ hρ
    rcases le_or_gt 0 ρ with hρ0 | hρ0
    · exact le_trans hspec (mul_le_mul_of_nonneg_right (hCmax_p i) hρ0)
    · exfalso; exact absurd (le_trans Metric.infDist_nonneg hρ) (by linarith)
  refine ⟨εt, 2 * εt, capR, hεtpos, by linarith, hcapRpos, hcapRfs, ?_⟩
  intro q hq
  rcases tube_cover_mem P hsimple hr hrclear h3r hsqreg hCmax_nn hCs hCp hcapbnd hcapR1 hq with
    h | h | h | h
  · exact Or.inl (Or.inl (by obtain ⟨i, hi⟩ := h; exact Set.mem_iUnion.mpr ⟨i, hi⟩))
  · exact Or.inl (Or.inr (by obtain ⟨i, hi⟩ := h; exact Set.mem_iUnion.mpr ⟨i, hi⟩))
  · exact Or.inr (Or.inl (by obtain ⟨i, hi⟩ := h; exact Set.mem_iUnion.mpr ⟨i, hi⟩))
  · exact Or.inr (Or.inr (by obtain ⟨i, hi⟩ := h; exact Set.mem_iUnion.mpr ⟨i, hi⟩))

/-- `√2 < 2`, used by the corner-meet lemmas' `εreg` clearance bounds. -/
private lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  rw [show (2:ℝ) = Real.sqrt 4 from by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **Small-angle datum for the corner-meet constructions.** A positive angle `η` below a
given `gap`, with `cos η ≥ 1/2`, `sin η ∈ (0, η]`, and the clearance `3·M·sin η < K·cos η`.
Factored out of the four corner-meet lemmas (their `η := min … / 2` setup blocks). -/
private lemma exists_corner_angle (M K gap : ℝ) (hM : 0 < M) (hK : 0 < K) (hgap : 0 < gap) :
    ∃ η : ℝ, 0 < η ∧ η < gap ∧ (1 : ℝ) / 2 ≤ Real.cos η ∧ 0 < Real.cos η ∧
      Real.sin η ≤ η ∧ 0 < Real.sin η ∧ 3 * M * Real.sin η < K * Real.cos η := by
  have hpi := Real.pi_pos
  have hKM : (0 : ℝ) < K / (6 * M) := by positivity
  set η := min (min (Real.pi / 3) (K / (6 * M))) gap / 2 with hηdef
  have hm1 : (0 : ℝ) < min (Real.pi / 3) (K / (6 * M)) := lt_min (by positivity) hKM
  have hle1 : min (min (Real.pi / 3) (K / (6 * M))) gap ≤ Real.pi / 3 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hle2 : min (min (Real.pi / 3) (K / (6 * M))) gap ≤ K / (6 * M) :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hle3 : min (min (Real.pi / 3) (K / (6 * M))) gap ≤ gap := min_le_right _ _
  have hm2 : (0 : ℝ) < min (min (Real.pi / 3) (K / (6 * M))) gap := lt_min hm1 hgap
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hηgap : η < gap := by rw [hηdef]; linarith
  have hηpi3 : η < Real.pi / 3 := by rw [hηdef]; linarith
  have hηK : η < K / (6 * M) := by rw [hηdef]; linarith
  have hcos : (1 : ℝ) / 2 ≤ Real.cos η := by
    have := Real.cos_le_cos_of_nonneg_of_le_pi hηpos.le (by linarith) hηpi3.le
    linarith [this, Real.cos_pi_div_three]
  have hcospos : 0 < Real.cos η := by linarith
  have hsinle : Real.sin η ≤ η := Real.sin_le hηpos.le
  have hsinpos : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hηpos (by linarith)
  refine ⟨η, hηpos, hηgap, hcos, hcospos, hsinle, hsinpos, ?_⟩
  -- `3M·sin η ≤ 3M·η < K/2 ≤ K·cos η`
  have h1 : 3 * M * Real.sin η ≤ 3 * M * η :=
    mul_le_mul_of_nonneg_left hsinle (by positivity)
  have h2 : η * (6 * M) < K := (lt_div_iff₀ (by positivity)).mp hηK
  have h3 : K * (1 / 2) ≤ K * Real.cos η := mul_le_mul_of_nonneg_left hcos hK.le
  linarith

/-- **Small-radius datum for the corner-meet constructions.** A positive radius `ρ` below
`capR` and `eD`, with `2ρ < εreg` and `4ρ < fs`. Factored out of the four corner-meet
lemmas (their `ρ := min … / 2` setup blocks). -/
private lemma exists_corner_radius (capR eD εreg fs : ℝ)
    (hcapR : 0 < capR) (heD : 0 < eD) (hεreg : 0 < εreg) (hfs : 0 < fs) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < capR ∧ ρ < eD ∧ 2 * ρ < εreg ∧ 4 * ρ < fs := by
  set m := min capR (min eD (min (εreg / 2) (fs / 4))) with hmdef
  have hmpos : 0 < m := lt_min hcapR (lt_min heD (lt_min (by linarith) (by linarith)))
  have h1 : m ≤ capR := min_le_left _ _
  have h2 : m ≤ eD := le_trans (min_le_right _ _) (min_le_left _ _)
  have h3 : m ≤ εreg / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : m ≤ fs / 4 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  exact ⟨m / 2, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Corner meet (left/capB).** The truncated left region beside edge `i` overlaps the
sector cap `B` at vertex `i+1`. Witness: a point `q = vert(i+1) + ρ·dirOf θ` with
`θ = α i + 2π − η` for a tiny `η` (so the offset direction is just inside the `capB` wedge
and just to the left/behind edge `i`) and `ρ` tiny. The `capB` membership is immediate from
the angle representative; the `leftRegion` membership uses `mem_leftRegion_of_nearFoot`, whose
clearance hypothesis reduces (binding edge `i+1`) to the trig inequality
`3·‖edgeDir i‖·sin η < K·cos η` and (every other edge) to feature size minus the small
foot-to-vertex distance. -/
lemma leftRegion_meet_capB (hsimple : P.IsSimple) (i : ZMod P.n) {εreg capR : ℝ}
    (hεreg : 0 < εreg) (hcapR : 0 < capR) (_hcapRfs : capR ≤ P.featureSize) :
    (P.leftRegion i εreg ∩ P.capB i capR).Nonempty := by
  set eD := eDist (P.edgeDir i) with heDdef
  have heDpos : 0 < eD := by rw [heDdef, eDist]; exact Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple i)
  set Msup := ‖P.edgeDir i‖ with hMsupdef
  have hMsuppos : 0 < Msup := norm_pos_iff.mpr (edgeDir_ne_zero P hsimple i)
  set N := (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 with hNdef
  have hNpos : 0 < N := normSq_edgeDir_pos P hsimple i
  have hNeD : N = eD ^ 2 := by rw [heDdef, eDist, Real.sq_sqrt (by positivity), hNdef]
  have hMle : Msup ≤ eD := by rw [hMsupdef, heDdef]; exact norm_le_eDist _
  obtain ⟨K, hKpos, hKbnd⟩ := infDist_succ_ge P hsimple i
  have hbeta : P.beta i < P.alpha i + 2 * Real.pi := beta_lt_alpha_add_2pi P hsimple i
  obtain ⟨η, hηpos, hηgap, -, hcospos, -, hsinpos, htrig⟩ :=
    exists_corner_angle Msup K (P.alpha i + 2 * Real.pi - P.beta i) hMsuppos hKpos (by linarith)
  set θ := P.alpha i + 2 * Real.pi - η with hθdef
  -- the small radius ρ; all constraints are linear since `t ≤ ρ` (using `Msup ≤ eD`)
  have hfspos : 0 < P.featureSize := featureSize_pos P hsimple
  obtain ⟨ρ, hρpos, hρcapR, hρeD, hρeps, hρfs⟩ :=
    exists_corner_radius capR eD εreg P.featureSize hcapR heDpos hεreg hfspos
  -- the witness point
  set q := toReal (P.vert (i + 1)) + ρ • dirOf θ with hqdef
  have hqsub : q - toReal (P.vert (i + 1)) = ρ • dirOf θ := by rw [hqdef]; abel
  have hqne : q ≠ toReal (P.vert (i + 1)) := by
    rw [← sub_ne_zero, hqsub]
    exact smul_ne_zero (ne_of_gt hρpos) (dirOf_ne_zero θ)
  -- capB membership
  have hcapBmem : q ∈ P.capB i capR := by
    refine mem_sectorCap_of_repr P i (θ := θ) hqne ⟨?_, ?_⟩ ?_ ?_
    · rw [hθdef]; linarith
    · rw [hθdef]; linarith
    · rw [hqsub, argOf_smul_dirOf_angle_eq hρpos]
    · rw [hqsub, eDist_smul, eDist_dirOf, mul_one, abs_of_pos hρpos]; exact hρcapR
  refine ⟨q, ?_, hcapBmem⟩
  -- leftRegion membership
  obtain ⟨s', t, hq, ht⟩ := rectMap_left_coords P hsimple i q
  -- cross value
  have hcrossval : cross (P.edgeDir i) (q - toReal (P.vert i)) = ρ * eD * Real.sin η := by
    have hqv : q - toReal (P.vert i) = ρ • dirOf θ + P.edgeDir i := by
      rw [hqdef, LatticePolygon.edgeDir]; abel
    rw [hqv, (isLinearMap_cross (P.edgeDir i)).map_add, (isLinearMap_cross (P.edgeDir i)).map_smul,
      show cross (P.edgeDir i) (P.edgeDir i) = 0 from by rw [cross]; ring, add_zero, smul_eq_mul]
    rw [show cross (P.edgeDir i) (dirOf θ) = eD * Real.sin η from by
      rw [heDdef]
      conv_lhs => rw [edgeDir_eq_neg_smul_dirOf_alpha P hsimple i]
      rw [cross_smul_left, cross_dirOf_dirOf,
        show θ - P.alpha i = 2 * Real.pi + (-η) from by rw [hθdef]; ring,
        Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
      simp [Real.sin_neg]]
    ring
  -- t value: t * N / Msup = cross = ρ eD sin η
  have htN : t * N / Msup = ρ * eD * Real.sin η := by rw [← hcrossval]; exact ht
  have htpos : 0 < t := by
    have : 0 < t * N / Msup := by rw [htN]; positivity
    by_contra hc; push Not at hc
    exact absurd (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc hNpos.le) hMsuppos.le) (by linarith)
  have htval : t = ρ * eD * Real.sin η * Msup / N := by
    rw [eq_div_iff (ne_of_gt hNpos), ← htN]; field_simp
  -- s' value: inner d (q - vert i) = s' * N
  have hinnerval : (P.edgeDir i).1 * (q - toReal (P.vert i)).1
      + (P.edgeDir i).2 * (q - toReal (P.vert i)).2 = N - ρ * eD * Real.cos η := by
    have hqv : q - toReal (P.vert i) = ρ • dirOf θ + P.edgeDir i := by
      rw [hqdef, LatticePolygon.edgeDir]; abel
    rw [hqv]
    have hinnerdir : (P.edgeDir i).1 * (dirOf θ).1 + (P.edgeDir i).2 * (dirOf θ).2 = -eD * Real.cos η := by
      rw [heDdef]
      conv_lhs => rw [edgeDir_eq_neg_smul_dirOf_alpha P hsimple i]
      rw [inner_smul_left, inner_dirOf_dirOf,
        show θ - P.alpha i = 2 * Real.pi + (-η) from by rw [hθdef]; ring,
        Real.cos_add, Real.sin_two_pi, Real.cos_two_pi]
      simp [Real.cos_neg]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hself : (P.edgeDir i).1 * (P.edgeDir i).1 + (P.edgeDir i).2 * (P.edgeDir i).2 = N := by
      rw [hNdef]; ring
    linear_combination ρ * hinnerdir + hself
  have hs'N : s' * N = N - ρ * eD * Real.cos η := by
    have hqi : (P.edgeDir i).1 * (q - toReal (P.vert i)).1
        + (P.edgeDir i).2 * (q - toReal (P.vert i)).2 = s' * N := by
      have hqv2 : q - toReal (P.vert i) = s' • P.edgeDir i + t • P.leftNormal i := by
        rw [hq, LatticePolygon.rectMap, LatticePolygon.edgeDir]; module
      have horth : (P.edgeDir i).1 * (P.leftNormal i).1 + (P.edgeDir i).2 * (P.leftNormal i).2 = 0 := by
        simp only [LatticePolygon.leftNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [hqv2]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have hself : (P.edgeDir i).1 * (P.edgeDir i).1 + (P.edgeDir i).2 * (P.edgeDir i).2 = N := by
        rw [hNdef]; ring
      linear_combination hself + t * horth
    rw [← hqi, hinnerval]
  have h1s' : 1 - s' = ρ * eD * Real.cos η / N := by
    rw [eq_div_iff (ne_of_gt hNpos)]; linear_combination -hs'N
  have h1s'pos : 0 < 1 - s' := by rw [h1s']; positivity
  -- bounds: t ≤ ρ (since Msup ≤ eD and sin η ≤ 1), 1-s' ≤ ρ / eD
  have htle : t ≤ ρ := by
    rw [htval, hNeD]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < eD ^ 2)]
    have hsin1 : Real.sin η * Msup ≤ 1 * eD :=
      mul_le_mul (Real.sin_le_one η) hMle hMsuppos.le zero_le_one
    linarith [mul_le_mul_of_nonneg_left hsin1 (by positivity : (0:ℝ) ≤ ρ * eD)]
  have h1s'bound : 1 - s' ≤ ρ / eD := by
    rw [h1s', hNeD]
    rw [div_le_div_iff₀ (by positivity) heDpos]
    rw [pow_two]
    linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
  -- s' ∈ (0,1)
  have hρeD1 : ρ / eD < 1 := by rw [div_lt_one heDpos]; exact hρeD
  have hs'lt1 : s' < 1 := by linarith [h1s'pos]
  have hs'gt0 : 0 < s' := by linarith [h1s'bound, hρeD1]
  have hs'Ioo : s' ∈ Set.Ioo (0:ℝ) 1 := ⟨hs'gt0, hs'lt1⟩
  -- cross positivity
  have hcrosspos : 0 < cross (P.edgeDir i) (q - toReal (P.vert i)) := by rw [hcrossval]; positivity
  -- δ := t, dist q (foot i s') = t
  have hδeq : dist q (P.foot i s') = t := dist_foot_eq_coord_left P hsimple i htpos.le hq
  -- √2 t < εreg
  have heps : Real.sqrt 2 * t < εreg := by
    have hsqrt2lt : Real.sqrt 2 < 2 := sqrt_two_lt_two
    have h1 : Real.sqrt 2 * t ≤ 2 * ρ := by
      calc Real.sqrt 2 * t ≤ Real.sqrt 2 * ρ :=
            mul_le_mul_of_nonneg_left htle (Real.sqrt_nonneg _)
        _ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (le_of_lt hsqrt2lt) (le_of_lt hρpos)
    linarith [hρeps, h1]
  -- the clearance hypothesis
  have hadj : ∀ j, j ≠ i → 3 * t < Metric.infDist (P.foot i s') (P.edgeSeg j) := by
    intro j hji
    by_cases hjsucc : j = i + 1
    · subst hjsucc
      have hKb := hKbnd s' hs'Ioo
      -- 3 t < K (1 - s')
      have hkey : 3 * t < K * (1 - s') := by
        have hpoly : 3 * (ρ * eD * Real.sin η * Msup) < K * (ρ * eD * Real.cos η) := by
          linarith [mul_lt_mul_of_pos_left htrig (mul_pos hρpos heDpos)]
        have ht3 : 3 * t = (3 * (ρ * eD * Real.sin η * Msup)) / N := by rw [htval]; ring
        have hk3 : K * (1 - s') = (K * (ρ * eD * Real.cos η)) / N := by rw [h1s']; ring
        rw [ht3, hk3, div_lt_div_iff_of_pos_right hNpos]
        exact hpoly
      linarith [hKb, hkey]
    · -- featureSize bound at vert(i+1)
      have hfs : P.featureSize ≤ Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j) :=
        featureSize_le P (i + 1) j hjsucc (by
          intro h; apply hji; rw [h]; ring)
      have hfoot_vert : dist (P.foot i s') (toReal (P.vert (i + 1))) ≤ ρ := by
        have heq : P.foot i s' - toReal (P.vert (i + 1)) = (-(1 - s')) • P.edgeDir i := by
          rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
        have hle : dist (P.foot i s') (toReal (P.vert (i + 1))) ≤ eDist (P.foot i s' - toReal (P.vert (i + 1))) := by
          rw [dist_eq_norm]; exact norm_le_eDist _
        rw [heq, eDist_smul, abs_neg, abs_of_nonneg (le_of_lt h1s'pos), ← heDdef] at hle
        have hub : (1 - s') * eD ≤ ρ := by
          rw [h1s', hNeD]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          rw [pow_two]
          linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
        linarith [hle, hub]
      have htri : Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j)
          ≤ Metric.infDist (P.foot i s') (P.edgeSeg j) + dist (toReal (P.vert (i + 1))) (P.foot i s') :=
        Metric.infDist_le_infDist_add_dist
      rw [dist_comm] at htri
      linarith [hfs, htri, hfoot_vert, htle, hρfs]
  exact mem_leftRegion_of_nearFoot P hsimple i hs'Ioo htpos hδeq hcrosspos heps hadj

/-- **Corner meet (right/capA).** Mirror of `leftRegion_meet_capB`: the truncated right region
beside edge `i` overlaps the sector cap `A` (the wedge `(α i, β i)`) at vertex `i+1`. Witness:
`q = vert(i+1) + ρ·dirOf θ` with `θ = α i + η` for a tiny `η` (just inside `capA`, just to the
right of edge `i`) and `ρ` tiny. -/
lemma rightRegion_meet_capA (hsimple : P.IsSimple) (i : ZMod P.n) {εreg capR : ℝ}
    (hεreg : 0 < εreg) (hcapR : 0 < capR) (_hcapRfs : capR ≤ P.featureSize) :
    (P.rightRegion i εreg ∩ P.capA i capR).Nonempty := by
  set eD := eDist (P.edgeDir i) with heDdef
  have heDpos : 0 < eD := by rw [heDdef, eDist]; exact Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple i)
  set Msup := ‖P.edgeDir i‖ with hMsupdef
  have hMsuppos : 0 < Msup := norm_pos_iff.mpr (edgeDir_ne_zero P hsimple i)
  set N := (P.edgeDir i).1 ^ 2 + (P.edgeDir i).2 ^ 2 with hNdef
  have hNpos : 0 < N := normSq_edgeDir_pos P hsimple i
  have hNeD : N = eD ^ 2 := by rw [heDdef, eDist, Real.sq_sqrt (by positivity), hNdef]
  have hMle : Msup ≤ eD := by rw [hMsupdef, heDdef]; exact norm_le_eDist _
  obtain ⟨K, hKpos, hKbnd⟩ := infDist_succ_ge P hsimple i
  have hab : P.alpha i < P.beta i := alpha_lt_beta P i
  obtain ⟨η, hηpos, hηgap, -, hcospos, -, hsinpos, htrig⟩ :=
    exists_corner_angle Msup K (P.beta i - P.alpha i) hMsuppos hKpos (by linarith)
  set θ := P.alpha i + η with hθdef
  have hfspos : 0 < P.featureSize := featureSize_pos P hsimple
  obtain ⟨ρ, hρpos, hρcapR, hρeD, hρeps, hρfs⟩ :=
    exists_corner_radius capR eD εreg P.featureSize hcapR heDpos hεreg hfspos
  -- the witness point
  set q := toReal (P.vert (i + 1)) + ρ • dirOf θ with hqdef
  have hqsub : q - toReal (P.vert (i + 1)) = ρ • dirOf θ := by rw [hqdef]; abel
  have hqne : q ≠ toReal (P.vert (i + 1)) := by
    rw [← sub_ne_zero, hqsub]; exact smul_ne_zero (ne_of_gt hρpos) (dirOf_ne_zero θ)
  -- capA membership
  have hcapAmem : q ∈ P.capA i capR := by
    refine mem_sectorCap_of_repr P i (θ := θ) hqne ⟨?_, ?_⟩ ?_ ?_
    · rw [hθdef]; linarith
    · rw [hθdef]; linarith
    · rw [hqsub, argOf_smul_dirOf_angle_eq hρpos]
    · rw [hqsub, eDist_smul, eDist_dirOf, mul_one, abs_of_pos hρpos]; exact hρcapR
  refine ⟨q, ?_, hcapAmem⟩
  -- rightRegion membership
  obtain ⟨s', t, hq, ht⟩ := rectMap_left_coords P hsimple i q
  -- cross value (negative for the right side)
  have hcrossval : cross (P.edgeDir i) (q - toReal (P.vert i)) = -(ρ * eD * Real.sin η) := by
    have hqv : q - toReal (P.vert i) = ρ • dirOf θ + P.edgeDir i := by
      rw [hqdef, LatticePolygon.edgeDir]; abel
    rw [hqv, (isLinearMap_cross (P.edgeDir i)).map_add, (isLinearMap_cross (P.edgeDir i)).map_smul,
      show cross (P.edgeDir i) (P.edgeDir i) = 0 from by rw [cross]; ring, add_zero, smul_eq_mul]
    rw [show cross (P.edgeDir i) (dirOf θ) = -(eD * Real.sin η) from by
      rw [heDdef]
      conv_lhs => rw [edgeDir_eq_neg_smul_dirOf_alpha P hsimple i]
      rw [cross_smul_left, cross_dirOf_dirOf, show θ - P.alpha i = η from by rw [hθdef]; ring]
      ring]
    ring
  have htN : t * N / Msup = -(ρ * eD * Real.sin η) := by rw [← hcrossval]; exact ht
  have htneg : t < 0 := by
    have hpos1 : 0 < ρ * eD * Real.sin η := by positivity
    have hlt : t * N / Msup < 0 := by rw [htN]; linarith
    by_contra hc; push Not at hc
    have : 0 ≤ t * N / Msup := by positivity
    linarith
  have htval : t = -(ρ * eD * Real.sin η * Msup / N) := by
    rw [show -(ρ * eD * Real.sin η * Msup / N) = (-(ρ * eD * Real.sin η)) * Msup / N from by ring,
      eq_div_iff (ne_of_gt hNpos), ← htN]; field_simp
  set δ := -t with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδval : δ = ρ * eD * Real.sin η * Msup / N := by rw [hδdef, htval]; ring
  -- s' value
  have hinnerval : (P.edgeDir i).1 * (q - toReal (P.vert i)).1
      + (P.edgeDir i).2 * (q - toReal (P.vert i)).2 = N - ρ * eD * Real.cos η := by
    have hqv : q - toReal (P.vert i) = ρ • dirOf θ + P.edgeDir i := by
      rw [hqdef, LatticePolygon.edgeDir]; abel
    rw [hqv]
    have hinnerdir : (P.edgeDir i).1 * (dirOf θ).1 + (P.edgeDir i).2 * (dirOf θ).2 = -eD * Real.cos η := by
      rw [heDdef]
      conv_lhs => rw [edgeDir_eq_neg_smul_dirOf_alpha P hsimple i]
      rw [inner_smul_left, inner_dirOf_dirOf, show θ - P.alpha i = η from by rw [hθdef]; ring]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hself : (P.edgeDir i).1 * (P.edgeDir i).1 + (P.edgeDir i).2 * (P.edgeDir i).2 = N := by
      rw [hNdef]; ring
    linear_combination ρ * hinnerdir + hself
  have hs'N : s' * N = N - ρ * eD * Real.cos η := by
    have hqi : (P.edgeDir i).1 * (q - toReal (P.vert i)).1
        + (P.edgeDir i).2 * (q - toReal (P.vert i)).2 = s' * N := by
      have hqv2 : q - toReal (P.vert i) = s' • P.edgeDir i + t • P.leftNormal i := by
        rw [hq, LatticePolygon.rectMap, LatticePolygon.edgeDir]; module
      have horth : (P.edgeDir i).1 * (P.leftNormal i).1 + (P.edgeDir i).2 * (P.leftNormal i).2 = 0 := by
        simp only [LatticePolygon.leftNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [hqv2]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have hself : (P.edgeDir i).1 * (P.edgeDir i).1 + (P.edgeDir i).2 * (P.edgeDir i).2 = N := by
        rw [hNdef]; ring
      linear_combination hself + t * horth
    rw [← hqi, hinnerval]
  have h1s' : 1 - s' = ρ * eD * Real.cos η / N := by
    rw [eq_div_iff (ne_of_gt hNpos)]; linear_combination -hs'N
  have h1s'pos : 0 < 1 - s' := by rw [h1s']; positivity
  have hδle : δ ≤ ρ := by
    rw [hδval, hNeD]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < eD ^ 2)]
    have hsin1 : Real.sin η * Msup ≤ 1 * eD :=
      mul_le_mul (Real.sin_le_one η) hMle hMsuppos.le zero_le_one
    linarith [mul_le_mul_of_nonneg_left hsin1 (by positivity : (0:ℝ) ≤ ρ * eD)]
  have h1s'bound : 1 - s' ≤ ρ / eD := by
    rw [h1s', hNeD]
    rw [div_le_div_iff₀ (by positivity) heDpos]
    rw [pow_two]
    linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
  have hρeD1 : ρ / eD < 1 := by rw [div_lt_one heDpos]; exact hρeD
  have hs'lt1 : s' < 1 := by linarith [h1s'pos]
  have hs'gt0 : 0 < s' := by linarith [h1s'bound, hρeD1]
  have hs'Ioo : s' ∈ Set.Ioo (0:ℝ) 1 := ⟨hs'gt0, hs'lt1⟩
  have hcrossneg : cross (P.edgeDir i) (q - toReal (P.vert i)) < 0 := by
    rw [hcrossval]
    have : 0 < ρ * eD * Real.sin η := by positivity
    linarith
  -- dist q (foot i s') = δ
  have hδeq : dist q (P.foot i s') = δ := by
    rw [hq, dist_rectMap_foot, leftNormal_unit P hsimple, mul_one, hδdef, abs_of_neg htneg]
  have heps : Real.sqrt 2 * δ < εreg := by
    have hsqrt2lt : Real.sqrt 2 < 2 := sqrt_two_lt_two
    have h1 : Real.sqrt 2 * δ ≤ 2 * ρ := by
      calc Real.sqrt 2 * δ ≤ Real.sqrt 2 * ρ := mul_le_mul_of_nonneg_left hδle (Real.sqrt_nonneg _)
        _ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (le_of_lt hsqrt2lt) (le_of_lt hρpos)
    linarith [hρeps, h1]
  have hadj : ∀ j, j ≠ i → 3 * δ < Metric.infDist (P.foot i s') (P.edgeSeg j) := by
    intro j hji
    by_cases hjsucc : j = i + 1
    · subst hjsucc
      have hKb := hKbnd s' hs'Ioo
      have hkey : 3 * δ < K * (1 - s') := by
        have hpoly : 3 * (ρ * eD * Real.sin η * Msup) < K * (ρ * eD * Real.cos η) := by
          linarith [mul_lt_mul_of_pos_left htrig (mul_pos hρpos heDpos)]
        have hd3 : 3 * δ = (3 * (ρ * eD * Real.sin η * Msup)) / N := by rw [hδval]; ring
        have hk3 : K * (1 - s') = (K * (ρ * eD * Real.cos η)) / N := by rw [h1s']; ring
        rw [hd3, hk3, div_lt_div_iff_of_pos_right hNpos]
        exact hpoly
      linarith [hKb, hkey]
    · have hfs : P.featureSize ≤ Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j) :=
        featureSize_le P (i + 1) j hjsucc (by intro h; apply hji; rw [h]; ring)
      have hfoot_vert : dist (P.foot i s') (toReal (P.vert (i + 1))) ≤ ρ := by
        have heq : P.foot i s' - toReal (P.vert (i + 1)) = (-(1 - s')) • P.edgeDir i := by
          rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
        have hle : dist (P.foot i s') (toReal (P.vert (i + 1))) ≤ eDist (P.foot i s' - toReal (P.vert (i + 1))) := by
          rw [dist_eq_norm]; exact norm_le_eDist _
        rw [heq, eDist_smul, abs_neg, abs_of_nonneg (le_of_lt h1s'pos), ← heDdef] at hle
        have hub : (1 - s') * eD ≤ ρ := by
          rw [h1s', hNeD]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          rw [pow_two]
          linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
        linarith [hle, hub]
      have htri : Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j)
          ≤ Metric.infDist (P.foot i s') (P.edgeSeg j) + dist (toReal (P.vert (i + 1))) (P.foot i s') :=
        Metric.infDist_le_infDist_add_dist
      rw [dist_comm] at htri
      linarith [hfs, htri, hfoot_vert, hδle, hρfs]
  exact mem_rightRegion_of_nearFoot P hsimple i hs'Ioo hδpos hδeq hcrossneg heps hadj

/-- **Corner meet (capB/left of next edge).** The sector cap `B` at vertex `i+1` overlaps the
truncated left region beside the *next* edge `i+1`. Witness: `q = vert(i+1) + ρ·dirOf θ` with
`θ = β i + η` for tiny `η` (just inside `capB` above the outgoing ray `β i`, hence just to the
left of edge `i+1` whose direction is `dirOf (β i)`). The foot lands near the *start* vertex of
edge `i+1` (`= vert(i+1)`), so the binding edge is the predecessor `i`, via `infDist_pred_ge`. -/
lemma capB_meet_leftRegion_succ (hsimple : P.IsSimple) (i : ZMod P.n) {εreg capR : ℝ}
    (hεreg : 0 < εreg) (hcapR : 0 < capR) (_hcapRfs : capR ≤ P.featureSize) :
    (P.capB i capR ∩ P.leftRegion (i + 1) εreg).Nonempty := by
  set eD := eDist (P.edgeDir (i + 1)) with heDdef
  have heDpos : 0 < eD := by rw [heDdef, eDist]; exact Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple (i + 1))
  set Msup := ‖P.edgeDir (i + 1)‖ with hMsupdef
  have hMsuppos : 0 < Msup := norm_pos_iff.mpr (edgeDir_ne_zero P hsimple (i + 1))
  set N := (P.edgeDir (i + 1)).1 ^ 2 + (P.edgeDir (i + 1)).2 ^ 2 with hNdef
  have hNpos : 0 < N := normSq_edgeDir_pos P hsimple (i + 1)
  have hNeD : N = eD ^ 2 := by rw [heDdef, eDist, Real.sq_sqrt (by positivity), hNdef]
  have hMle : Msup ≤ eD := by rw [hMsupdef, heDdef]; exact norm_le_eDist _
  obtain ⟨K, hKpos, hKbnd⟩ := infDist_pred_ge P hsimple (i + 1)
  have hbeta : P.beta i < P.alpha i + 2 * Real.pi := beta_lt_alpha_add_2pi P hsimple i
  obtain ⟨η, hηpos, hηgap, -, hcospos, -, hsinpos, htrig⟩ :=
    exists_corner_angle Msup K (P.alpha i + 2 * Real.pi - P.beta i) hMsuppos hKpos (by linarith)
  set θ := P.beta i + η with hθdef
  have hfspos : 0 < P.featureSize := featureSize_pos P hsimple
  obtain ⟨ρ, hρpos, hρcapR, hρeD, hρeps, hρfs⟩ :=
    exists_corner_radius capR eD εreg P.featureSize hcapR heDpos hεreg hfspos
  -- the witness point
  set q := toReal (P.vert (i + 1)) + ρ • dirOf θ with hqdef
  have hqsub : q - toReal (P.vert (i + 1)) = ρ • dirOf θ := by rw [hqdef]; abel
  have hqne : q ≠ toReal (P.vert (i + 1)) := by
    rw [← sub_ne_zero, hqsub]; exact smul_ne_zero (ne_of_gt hρpos) (dirOf_ne_zero θ)
  -- capB membership
  have hcapBmem : q ∈ P.capB i capR := by
    refine mem_sectorCap_of_repr P i (θ := θ) hqne ⟨?_, ?_⟩ ?_ ?_
    · rw [hθdef]; linarith
    · rw [hθdef]; linarith
    · rw [hqsub, argOf_smul_dirOf_angle_eq hρpos]
    · rw [hqsub, eDist_smul, eDist_dirOf, mul_one, abs_of_pos hρpos]; exact hρcapR
  refine ⟨q, hcapBmem, ?_⟩
  -- leftRegion (i+1) membership
  obtain ⟨s', t, hq, ht⟩ := rectMap_left_coords P hsimple (i + 1) q
  -- cross value (positive: left of edge i+1)
  have hcrossval : cross (P.edgeDir (i + 1)) (q - toReal (P.vert (i + 1))) = ρ * eD * Real.sin η := by
    rw [hqsub, (isLinearMap_cross (P.edgeDir (i + 1))).map_smul, smul_eq_mul]
    rw [show cross (P.edgeDir (i + 1)) (dirOf θ) = eD * Real.sin η from by
      rw [heDdef]
      conv_lhs => rw [edgeDir_succ_eq_smul_dirOf_beta P hsimple i]
      rw [cross_smul_left, cross_dirOf_dirOf, show θ - P.beta i = η from by rw [hθdef]; ring]]
    ring
  have htN : t * N / Msup = ρ * eD * Real.sin η := by rw [← hcrossval]; exact ht
  have htpos : 0 < t := by
    have : 0 < t * N / Msup := by rw [htN]; positivity
    by_contra hc; push Not at hc
    exact absurd (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc hNpos.le) hMsuppos.le) (by linarith)
  have htval : t = ρ * eD * Real.sin η * Msup / N := by
    rw [eq_div_iff (ne_of_gt hNpos), ← htN]; field_simp
  -- s' value: inner = s' * N = ρ eD cos η
  have hinnerval : (P.edgeDir (i + 1)).1 * (q - toReal (P.vert (i + 1))).1
      + (P.edgeDir (i + 1)).2 * (q - toReal (P.vert (i + 1))).2 = ρ * eD * Real.cos η := by
    rw [hqsub]
    have hinnerdir : (P.edgeDir (i + 1)).1 * (dirOf θ).1 + (P.edgeDir (i + 1)).2 * (dirOf θ).2 = eD * Real.cos η := by
      rw [heDdef]
      conv_lhs => rw [edgeDir_succ_eq_smul_dirOf_beta P hsimple i]
      rw [inner_smul_left, inner_dirOf_dirOf, show θ - P.beta i = η from by rw [hθdef]; ring]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination ρ * hinnerdir
  have hs'N : s' * N = ρ * eD * Real.cos η := by
    have hqi : (P.edgeDir (i + 1)).1 * (q - toReal (P.vert (i + 1))).1
        + (P.edgeDir (i + 1)).2 * (q - toReal (P.vert (i + 1))).2 = s' * N := by
      have hqv2 : q - toReal (P.vert (i + 1)) = s' • P.edgeDir (i + 1) + t • P.leftNormal (i + 1) := by
        rw [hq, LatticePolygon.rectMap, LatticePolygon.edgeDir]; module
      have horth : (P.edgeDir (i + 1)).1 * (P.leftNormal (i + 1)).1
          + (P.edgeDir (i + 1)).2 * (P.leftNormal (i + 1)).2 = 0 := by
        simp only [LatticePolygon.leftNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [hqv2]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have hself : (P.edgeDir (i + 1)).1 * (P.edgeDir (i + 1)).1
          + (P.edgeDir (i + 1)).2 * (P.edgeDir (i + 1)).2 = N := by rw [hNdef]; ring
      linear_combination hself + t * horth
    rw [← hqi, hinnerval]
  have hs'val : s' = ρ * eD * Real.cos η / N := by
    rw [eq_div_iff (ne_of_gt hNpos)]; linear_combination hs'N
  have hs'pos : 0 < s' := by rw [hs'val]; positivity
  have htle : t ≤ ρ := by
    rw [htval, hNeD]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < eD ^ 2)]
    have hsin1 : Real.sin η * Msup ≤ 1 * eD :=
      mul_le_mul (Real.sin_le_one η) hMle hMsuppos.le zero_le_one
    linarith [mul_le_mul_of_nonneg_left hsin1 (by positivity : (0:ℝ) ≤ ρ * eD)]
  have hs'bound : s' ≤ ρ / eD := by
    rw [hs'val, hNeD]
    rw [div_le_div_iff₀ (by positivity) heDpos]
    rw [pow_two]
    linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
  have hρeD1 : ρ / eD < 1 := by rw [div_lt_one heDpos]; exact hρeD
  have hs'lt1 : s' < 1 := by linarith [hs'bound, hρeD1]
  have hs'Ioo : s' ∈ Set.Ioo (0:ℝ) 1 := ⟨hs'pos, hs'lt1⟩
  have hcrosspos : 0 < cross (P.edgeDir (i + 1)) (q - toReal (P.vert (i + 1))) := by rw [hcrossval]; positivity
  have hδeq : dist q (P.foot (i + 1) s') = t := dist_foot_eq_coord_left P hsimple (i + 1) htpos.le hq
  have heps : Real.sqrt 2 * t < εreg := by
    have hsqrt2lt : Real.sqrt 2 < 2 := sqrt_two_lt_two
    have h1 : Real.sqrt 2 * t ≤ 2 * ρ := by
      calc Real.sqrt 2 * t ≤ Real.sqrt 2 * ρ := mul_le_mul_of_nonneg_left htle (Real.sqrt_nonneg _)
        _ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (le_of_lt hsqrt2lt) (le_of_lt hρpos)
    linarith [hρeps, h1]
  have hadj : ∀ j, j ≠ i + 1 → 3 * t < Metric.infDist (P.foot (i + 1) s') (P.edgeSeg j) := by
    intro j hji
    by_cases hjpred : j = i
    · subst j
      have hKb := hKbnd s' hs'Ioo
      have hkey : 3 * t < K * s' := by
        have hpoly : 3 * (ρ * eD * Real.sin η * Msup) < K * (ρ * eD * Real.cos η) := by
          linarith [mul_lt_mul_of_pos_left htrig (mul_pos hρpos heDpos)]
        have ht3 : 3 * t = (3 * (ρ * eD * Real.sin η * Msup)) / N := by rw [htval]; ring
        have hk3 : K * s' = (K * (ρ * eD * Real.cos η)) / N := by rw [hs'val]; ring
        rw [ht3, hk3, div_lt_div_iff_of_pos_right hNpos]
        exact hpoly
      have hpred : Metric.infDist (P.foot (i + 1) s') (P.edgeSeg ((i + 1) - 1)) =
          Metric.infDist (P.foot (i + 1) s') (P.edgeSeg i) := by rw [add_sub_cancel_right]
      rw [← hpred]; linarith [hKb, hkey]
    · -- featureSize at vert(i+1) (start vertex of edge i+1)
      have hfs : P.featureSize ≤ Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j) :=
        featureSize_le P (i + 1) j hji (by
          intro h; apply hjpred; rw [h]; ring)
      have hfoot_vert : dist (P.foot (i + 1) s') (toReal (P.vert (i + 1))) ≤ ρ := by
        have heq : P.foot (i + 1) s' - toReal (P.vert (i + 1)) = s' • P.edgeDir (i + 1) := by
          rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
        have hle : dist (P.foot (i + 1) s') (toReal (P.vert (i + 1)))
            ≤ eDist (P.foot (i + 1) s' - toReal (P.vert (i + 1))) := by
          rw [dist_eq_norm]; exact norm_le_eDist _
        rw [heq, eDist_smul, abs_of_nonneg (le_of_lt hs'pos), ← heDdef] at hle
        have hub : s' * eD ≤ ρ := by
          rw [hs'val, hNeD]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          rw [pow_two]
          linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
        linarith [hle, hub]
      have htri : Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j)
          ≤ Metric.infDist (P.foot (i + 1) s') (P.edgeSeg j) + dist (toReal (P.vert (i + 1))) (P.foot (i + 1) s') :=
        Metric.infDist_le_infDist_add_dist
      rw [dist_comm] at htri
      linarith [hfs, htri, hfoot_vert, htle, hρfs]
  exact mem_leftRegion_of_nearFoot P hsimple (i + 1) hs'Ioo htpos hδeq hcrosspos heps hadj

/-- **Corner meet (capA/right of next edge).** Mirror of `capB_meet_leftRegion_succ`: the sector
cap `A` at vertex `i+1` overlaps the truncated right region beside the next edge `i+1`. Witness:
`q = vert(i+1) + ρ·dirOf θ` with `θ = β i − η` (just inside `capA` below the outgoing ray, hence
just to the right of edge `i+1`). The foot lands near the start vertex; binding edge is `i`. -/
lemma capA_meet_rightRegion_succ (hsimple : P.IsSimple) (i : ZMod P.n) {εreg capR : ℝ}
    (hεreg : 0 < εreg) (hcapR : 0 < capR) (_hcapRfs : capR ≤ P.featureSize) :
    (P.capA i capR ∩ P.rightRegion (i + 1) εreg).Nonempty := by
  set eD := eDist (P.edgeDir (i + 1)) with heDdef
  have heDpos : 0 < eD := by rw [heDdef, eDist]; exact Real.sqrt_pos.mpr (normSq_edgeDir_pos P hsimple (i + 1))
  set Msup := ‖P.edgeDir (i + 1)‖ with hMsupdef
  have hMsuppos : 0 < Msup := norm_pos_iff.mpr (edgeDir_ne_zero P hsimple (i + 1))
  set N := (P.edgeDir (i + 1)).1 ^ 2 + (P.edgeDir (i + 1)).2 ^ 2 with hNdef
  have hNpos : 0 < N := normSq_edgeDir_pos P hsimple (i + 1)
  have hNeD : N = eD ^ 2 := by rw [heDdef, eDist, Real.sq_sqrt (by positivity), hNdef]
  have hMle : Msup ≤ eD := by rw [hMsupdef, heDdef]; exact norm_le_eDist _
  obtain ⟨K, hKpos, hKbnd⟩ := infDist_pred_ge P hsimple (i + 1)
  have hab : P.alpha i < P.beta i := alpha_lt_beta P i
  obtain ⟨η, hηpos, hηgap, -, hcospos, -, hsinpos, htrig⟩ :=
    exists_corner_angle Msup K (P.beta i - P.alpha i) hMsuppos hKpos (by linarith)
  set θ := P.beta i - η with hθdef
  have hfspos : 0 < P.featureSize := featureSize_pos P hsimple
  obtain ⟨ρ, hρpos, hρcapR, hρeD, hρeps, hρfs⟩ :=
    exists_corner_radius capR eD εreg P.featureSize hcapR heDpos hεreg hfspos
  set q := toReal (P.vert (i + 1)) + ρ • dirOf θ with hqdef
  have hqsub : q - toReal (P.vert (i + 1)) = ρ • dirOf θ := by rw [hqdef]; abel
  have hqne : q ≠ toReal (P.vert (i + 1)) := by
    rw [← sub_ne_zero, hqsub]; exact smul_ne_zero (ne_of_gt hρpos) (dirOf_ne_zero θ)
  -- capA membership
  have hcapAmem : q ∈ P.capA i capR := by
    refine mem_sectorCap_of_repr P i (θ := θ) hqne ⟨?_, ?_⟩ ?_ ?_
    · rw [hθdef]; linarith
    · rw [hθdef]; linarith
    · rw [hqsub, argOf_smul_dirOf_angle_eq hρpos]
    · rw [hqsub, eDist_smul, eDist_dirOf, mul_one, abs_of_pos hρpos]; exact hρcapR
  refine ⟨q, hcapAmem, ?_⟩
  -- rightRegion (i+1) membership
  obtain ⟨s', t, hq, ht⟩ := rectMap_left_coords P hsimple (i + 1) q
  have hcrossval : cross (P.edgeDir (i + 1)) (q - toReal (P.vert (i + 1))) = -(ρ * eD * Real.sin η) := by
    rw [hqsub, (isLinearMap_cross (P.edgeDir (i + 1))).map_smul, smul_eq_mul]
    rw [show cross (P.edgeDir (i + 1)) (dirOf θ) = -(eD * Real.sin η) from by
      rw [heDdef]
      conv_lhs => rw [edgeDir_succ_eq_smul_dirOf_beta P hsimple i]
      rw [cross_smul_left, cross_dirOf_dirOf, show θ - P.beta i = -η from by rw [hθdef]; ring,
        Real.sin_neg]; ring]
    ring
  have htN : t * N / Msup = -(ρ * eD * Real.sin η) := by rw [← hcrossval]; exact ht
  have htneg : t < 0 := by
    have hpos1 : 0 < ρ * eD * Real.sin η := by positivity
    have hlt : t * N / Msup < 0 := by rw [htN]; linarith
    by_contra hc; push Not at hc
    have : 0 ≤ t * N / Msup := by positivity
    linarith
  have htval : t = -(ρ * eD * Real.sin η * Msup / N) := by
    rw [show -(ρ * eD * Real.sin η * Msup / N) = (-(ρ * eD * Real.sin η)) * Msup / N from by ring,
      eq_div_iff (ne_of_gt hNpos), ← htN]; field_simp
  set δ := -t with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδval : δ = ρ * eD * Real.sin η * Msup / N := by rw [hδdef, htval]; ring
  have hinnerval : (P.edgeDir (i + 1)).1 * (q - toReal (P.vert (i + 1))).1
      + (P.edgeDir (i + 1)).2 * (q - toReal (P.vert (i + 1))).2 = ρ * eD * Real.cos η := by
    rw [hqsub]
    have hinnerdir : (P.edgeDir (i + 1)).1 * (dirOf θ).1 + (P.edgeDir (i + 1)).2 * (dirOf θ).2 = eD * Real.cos η := by
      rw [heDdef]
      conv_lhs => rw [edgeDir_succ_eq_smul_dirOf_beta P hsimple i]
      rw [inner_smul_left, inner_dirOf_dirOf, show θ - P.beta i = -η from by rw [hθdef]; ring,
        Real.cos_neg]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination ρ * hinnerdir
  have hs'N : s' * N = ρ * eD * Real.cos η := by
    have hqi : (P.edgeDir (i + 1)).1 * (q - toReal (P.vert (i + 1))).1
        + (P.edgeDir (i + 1)).2 * (q - toReal (P.vert (i + 1))).2 = s' * N := by
      have hqv2 : q - toReal (P.vert (i + 1)) = s' • P.edgeDir (i + 1) + t • P.leftNormal (i + 1) := by
        rw [hq, LatticePolygon.rectMap, LatticePolygon.edgeDir]; module
      have horth : (P.edgeDir (i + 1)).1 * (P.leftNormal (i + 1)).1
          + (P.edgeDir (i + 1)).2 * (P.leftNormal (i + 1)).2 = 0 := by
        simp only [LatticePolygon.leftNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [hqv2]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have hself : (P.edgeDir (i + 1)).1 * (P.edgeDir (i + 1)).1
          + (P.edgeDir (i + 1)).2 * (P.edgeDir (i + 1)).2 = N := by rw [hNdef]; ring
      linear_combination hself + t * horth
    rw [← hqi, hinnerval]
  have hs'val : s' = ρ * eD * Real.cos η / N := by
    rw [eq_div_iff (ne_of_gt hNpos)]; linear_combination hs'N
  have hs'pos : 0 < s' := by rw [hs'val]; positivity
  have hδle : δ ≤ ρ := by
    rw [hδval, hNeD]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < eD ^ 2)]
    have hsin1 : Real.sin η * Msup ≤ 1 * eD :=
      mul_le_mul (Real.sin_le_one η) hMle hMsuppos.le zero_le_one
    linarith [mul_le_mul_of_nonneg_left hsin1 (by positivity : (0:ℝ) ≤ ρ * eD)]
  have hs'bound : s' ≤ ρ / eD := by
    rw [hs'val, hNeD]
    rw [div_le_div_iff₀ (by positivity) heDpos]
    rw [pow_two]
    linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
  have hρeD1 : ρ / eD < 1 := by rw [div_lt_one heDpos]; exact hρeD
  have hs'lt1 : s' < 1 := by linarith [hs'bound, hρeD1]
  have hs'Ioo : s' ∈ Set.Ioo (0:ℝ) 1 := ⟨hs'pos, hs'lt1⟩
  have hcrossneg : cross (P.edgeDir (i + 1)) (q - toReal (P.vert (i + 1))) < 0 := by
    rw [hcrossval]
    have : 0 < ρ * eD * Real.sin η := by positivity
    linarith
  have hδeq : dist q (P.foot (i + 1) s') = δ := by
    rw [hq, dist_rectMap_foot, leftNormal_unit P hsimple, mul_one, hδdef, abs_of_neg htneg]
  have heps : Real.sqrt 2 * δ < εreg := by
    have hsqrt2lt : Real.sqrt 2 < 2 := sqrt_two_lt_two
    have h1 : Real.sqrt 2 * δ ≤ 2 * ρ := by
      calc Real.sqrt 2 * δ ≤ Real.sqrt 2 * ρ := mul_le_mul_of_nonneg_left hδle (Real.sqrt_nonneg _)
        _ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (le_of_lt hsqrt2lt) (le_of_lt hρpos)
    linarith [hρeps, h1]
  have hadj : ∀ j, j ≠ i + 1 → 3 * δ < Metric.infDist (P.foot (i + 1) s') (P.edgeSeg j) := by
    intro j hji
    by_cases hjpred : j = i
    · subst j
      have hKb := hKbnd s' hs'Ioo
      have hkey : 3 * δ < K * s' := by
        have hpoly : 3 * (ρ * eD * Real.sin η * Msup) < K * (ρ * eD * Real.cos η) := by
          linarith [mul_lt_mul_of_pos_left htrig (mul_pos hρpos heDpos)]
        have hd3 : 3 * δ = (3 * (ρ * eD * Real.sin η * Msup)) / N := by rw [hδval]; ring
        have hk3 : K * s' = (K * (ρ * eD * Real.cos η)) / N := by rw [hs'val]; ring
        rw [hd3, hk3, div_lt_div_iff_of_pos_right hNpos]
        exact hpoly
      have hpred : Metric.infDist (P.foot (i + 1) s') (P.edgeSeg ((i + 1) - 1)) =
          Metric.infDist (P.foot (i + 1) s') (P.edgeSeg i) := by rw [add_sub_cancel_right]
      rw [← hpred]; linarith [hKb, hkey]
    · have hfs : P.featureSize ≤ Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j) :=
        featureSize_le P (i + 1) j hji (by intro h; apply hjpred; rw [h]; ring)
      have hfoot_vert : dist (P.foot (i + 1) s') (toReal (P.vert (i + 1))) ≤ ρ := by
        have heq : P.foot (i + 1) s' - toReal (P.vert (i + 1)) = s' • P.edgeDir (i + 1) := by
          rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
        have hle : dist (P.foot (i + 1) s') (toReal (P.vert (i + 1)))
            ≤ eDist (P.foot (i + 1) s' - toReal (P.vert (i + 1))) := by
          rw [dist_eq_norm]; exact norm_le_eDist _
        rw [heq, eDist_smul, abs_of_nonneg (le_of_lt hs'pos), ← heDdef] at hle
        have hub : s' * eD ≤ ρ := by
          rw [hs'val, hNeD]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          rw [pow_two]
          linarith [mul_le_mul_of_nonneg_left (Real.cos_le_one η) (by positivity : (0:ℝ) ≤ ρ * eD * eD)]
        linarith [hle, hub]
      have htri : Metric.infDist (toReal (P.vert (i + 1))) (P.edgeSeg j)
          ≤ Metric.infDist (P.foot (i + 1) s') (P.edgeSeg j) + dist (toReal (P.vert (i + 1))) (P.foot (i + 1) s') :=
        Metric.infDist_le_infDist_add_dist
      rw [dist_comm] at htri
      linarith [hfs, htri, hfoot_vert, hδle, hρfs]
  exact mem_rightRegion_of_nearFoot P hsimple (i + 1) hs'Ioo hδpos hδeq hcrossneg heps hadj

/-- **`L = ⋃ leftRegion ∪ ⋃ capB` is off-boundary.** -/
lemma left_half_subset_compl_boundary (hsimple : P.IsSimple) {εreg capR : ℝ}
    (hcapRfs : capR ≤ P.featureSize) :
    ((⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR)) ⊆ P.boundaryᶜ := by
  apply Set.union_subset
  · exact Set.iUnion_subset (fun i => leftRegion_subset_compl_boundary P hsimple i)
  · exact Set.iUnion_subset (fun i => capB_subset_compl_boundary P hsimple i hcapRfs)

/-- **`R = ⋃ rightRegion ∪ ⋃ capA` is off-boundary.** -/
lemma right_half_subset_compl_boundary (hsimple : P.IsSimple) {εreg capR : ℝ}
    (hcapRfs : capR ≤ P.featureSize) :
    ((⋃ i, P.rightRegion i εreg) ∪ (⋃ i, P.capA i capR)) ⊆ P.boundaryᶜ := by
  apply Set.union_subset
  · exact Set.iUnion_subset (fun i => rightRegion_subset_compl_boundary P hsimple i)
  · exact Set.iUnion_subset (fun i => capA_subset_compl_boundary P hsimple i hcapRfs)

/-- **`compl_boundary_atMost_two` from the meet families.** Given the cyclic meets linking each
edge-region to its corner caps, the complement of the boundary is the union of two preconnected
sets. This is the topological assembly; the four meet hypotheses are the remaining geometric
input (each region overlaps the corner cap that continues it around the shared vertex). -/
theorem compl_boundary_atMost_two_of_meets (hsimple : P.IsSimple)
    {εt εreg capR : ℝ} (hεt : 0 < εt) (hcapRfs : capR ≤ P.featureSize)
    (hεregpos : 0 < εreg) (hcapRpos : 0 < capR)
    (hcover : P.Tube εt ⊆ ((⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR)) ∪
                  ((⋃ i, P.rightRegion i εreg) ∪ (⋃ i, P.capA i capR)))
    (hmeetL1 : ∀ i, (P.leftRegion i εreg ∩ P.capB i capR).Nonempty)
    (hmeetL2 : ∀ i, (P.capB i capR ∩ P.leftRegion (i + 1) εreg).Nonempty)
    (hmeetR1 : ∀ i, (P.rightRegion i εreg ∩ P.capA i capR).Nonempty)
    (hmeetR2 : ∀ i, (P.capA i capR ∩ P.rightRegion (i + 1) εreg).Nonempty) :
    ∃ A B : Set (ℝ × ℝ), A ∪ B = P.boundaryᶜ ∧ IsPreconnected A ∧ IsPreconnected B := by
  have hLpc : IsPathConnected ((⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR)) :=
    isPathConnected_region_cap_cycle P
      (fun i => isPathConnected_leftRegion P hsimple i hεregpos)
      (fun i => isPathConnected_capB P hsimple i hcapRpos) hmeetL1 hmeetL2
  have hRpc : IsPathConnected ((⋃ i, P.rightRegion i εreg) ∪ (⋃ i, P.capA i capR)) :=
    isPathConnected_region_cap_cycle P
      (fun i => isPathConnected_rightRegion P hsimple i hεregpos)
      (fun i => isPathConnected_capA P hsimple i hcapRpos) hmeetR1 hmeetR2
  exact compl_boundary_atMost_two_of_tube_cover P hεt hcover
    (left_half_subset_compl_boundary P hsimple hcapRfs)
    (right_half_subset_compl_boundary P hsimple hcapRfs) hLpc hRpc

/-- **Polygonal Jordan curve theorem, ≤2 direction.** The complement of a simple lattice
polygon's boundary is the union of two preconnected sets. Combining the tube cover
(`exists_tube_cover`) with the four corner meets (`leftRegion_meet_capB`,
`capB_meet_leftRegion_succ`, `rightRegion_meet_capA`, `capA_meet_rightRegion_succ`), the two
half-tubes `L = ⋃ leftRegion ∪ ⋃ capB` and `R = ⋃ rightRegion ∪ ⋃ capA` are each
path-connected and together cover `boundaryᶜ`. -/
theorem compl_boundary_atMost_two (hsimple : P.IsSimple) :
    ∃ A B : Set (ℝ × ℝ), A ∪ B = P.boundaryᶜ ∧ IsPreconnected A ∧ IsPreconnected B := by
  obtain ⟨εt, εreg, capR, hεt, hεreg, hcapR, hcapRfs, hcover⟩ := exists_tube_cover P hsimple
  exact compl_boundary_atMost_two_of_meets P hsimple hεt hcapRfs hεreg hcapR hcover
    (fun i => leftRegion_meet_capB P hsimple i hεreg hcapR hcapRfs)
    (fun i => capB_meet_leftRegion_succ P hsimple i hεreg hcapR hcapRfs)
    (fun i => rightRegion_meet_capA P hsimple i hεreg hcapR hcapRfs)
    (fun i => capA_meet_rightRegion_succ P hsimple i hεreg hcapR hcapRfs)

/-- **Some off-boundary point has winding `0`.** From `winding_zero_on_cobounded`
there is a radius beyond which the winding vanishes; any point far enough out (and
necessarily off the bounded boundary) witnesses winding `0`. -/
lemma exists_offBoundary_winding_zero (_ : P.IsSimple) :
    ∃ q : ℝ × ℝ, q ∉ P.boundary ∧ P.winding q = 0 := by
  obtain ⟨R, hR⟩ := winding_zero_on_cobounded P
  -- the boundary is a finite union of segments, hence bounded
  have hbd : Bornology.IsBounded P.boundary := by
    unfold LatticePolygon.boundary
    rw [Bornology.isBounded_iUnion]
    intro i
    unfold LatticePolygon.edgeSeg
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isBounded
  obtain ⟨Rb, hRb⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hbd
  set c : ℝ := |R| + |Rb| + 1 with hc
  have hcnn : (0 : ℝ) ≤ c := by positivity
  have hcnorm : ‖((c : ℝ), (0 : ℝ))‖ = c := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_zero,
      max_eq_left (abs_nonneg _), abs_of_nonneg hcnn]
  have hcR : R < c := by rw [hc]; have := le_abs_self R; have := abs_nonneg Rb; linarith
  have hcRb : Rb < c := by rw [hc]; have := le_abs_self Rb; have := abs_nonneg R; linarith
  refine ⟨(c, 0), ?_, ?_⟩
  · intro hq
    have hmem := hRb hq
    rw [Metric.mem_closedBall, dist_zero_right, hcnorm] at hmem
    linarith
  · exact hR (c, 0) (by rw [hcnorm]; exact hcR)

/-- **Winding bound, unsigned half.** For a simple, positively-oriented polygon every
off-boundary point has winding `∈ {0, v}` where `v = ±1` is the witness value. Uses
that `boundaryᶜ` is covered by the two preconnected pieces (`compl_boundary_atMost_two`),
on each of which `winding` is constant (`winding_const_of_isPreconnected`); since there
are only two pieces there are at most two values, and the far point (`winding 0`) and the
witness (`winding ±1`) pin them to `{0, v}`. -/
lemma winding_mem_zero_or_witness (hsimple : P.IsSimple) (horient : P.PositivelyOriented) :
    ∃ v : ℤ, (v = 1 ∨ v = -1) ∧ ∀ q : ℝ × ℝ, q ∉ P.boundary →
      P.winding q = 0 ∨ P.winding q = v := by
  classical
  obtain ⟨A, B, hAB, hApre, hBpre⟩ := compl_boundary_atMost_two P hsimple
  obtain ⟨q0, hq0b, hq0w⟩ := exists_offBoundary_winding_zero P hsimple
  obtain ⟨w, hwb, hwabs⟩ := exists_abs_winding_eq_one P hsimple horient
  set v := P.winding w with hv
  refine ⟨v, hwabs, ?_⟩
  -- A, B ⊆ boundaryᶜ
  have hAsub : A ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_left
  have hBsub : B ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_right
  -- membership of the three distinguished points in A ∪ B
  have hq0mem : q0 ∈ A ∪ B := by rw [hAB]; exact hq0b
  have hwmem : w ∈ A ∪ B := by rw [hAB]; exact hwb
  -- `winding` constant on A and on B
  have hconstA : ∀ x ∈ A, ∀ y ∈ A, P.winding x = P.winding y := fun x hx y hy =>
    winding_const_of_isPreconnected P hAsub hApre hx hy
  have hconstB : ∀ x ∈ B, ∀ y ∈ B, P.winding x = P.winding y := fun x hx y hy =>
    winding_const_of_isPreconnected P hBsub hBpre hx hy
  have hv01 : v = 1 ∨ v = -1 := hwabs
  have hvne : v ≠ 0 := by rcases hv01 with h | h <;> rw [h] <;> decide
  intro q hqb
  have hqmem : q ∈ A ∪ B := by rw [hAB]; exact hqb
  -- For any point in A ∪ B, its winding equals that of q0 (0) or of w (v).
  rcases hqmem with hqA | hqB <;> rcases hq0mem with h0A | h0B <;>
    rcases hwmem with hwA | hwB
  -- q∈A, q0∈A, w∈A
  · left; rw [hconstA q hqA q0 h0A]; exact hq0w
  -- q∈A, q0∈A, w∈B
  · left; rw [hconstA q hqA q0 h0A]; exact hq0w
  -- q∈A, q0∈B, w∈A
  · right; rw [hconstA q hqA w hwA]
  -- q∈A, q0∈B, w∈B : then vA unknown, but vB=0 and vB=v ⟹ contradiction unless...
  · exfalso
    have : P.winding w = P.winding q0 := hconstB w hwB q0 h0B
    rw [hq0w] at this; exact hvne this
  -- q∈B, q0∈A, w∈A : vB unknown; vA=0 and vA=v ⟹ contradiction
  · exfalso
    have : P.winding w = P.winding q0 := hconstA w hwA q0 h0A
    rw [hq0w] at this; exact hvne this
  -- q∈B, q0∈A, w∈B
  · right; rw [hconstB q hqB w hwB]
  -- q∈B, q0∈B, w∈A
  · left; rw [hconstB q hqB q0 h0B]; exact hq0w
  -- q∈B, q0∈B, w∈B
  · left; rw [hconstB q hqB q0 h0B]; exact hq0w

/-- **A generic height with a nonempty spanning set (orientation-free).** Every
simple polygon has a generic height `y` (no vertex on the line) at which some edge
spans. Take the lex-lowest vertex `m` and a generic `y` in the lowest band
`(yₘ, yₘ+1)`. At least one neighbour of `vₘ` is strictly above `yₘ`: otherwise both
incident vectors lie on the positive `x`-axis, forcing `cornerCross P m = 0`,
contradicting `cornerCross_ne_zero_lex_lowest`. The strictly-above neighbour's edge
spans `y` (`spanning_at_lowest_band`). -/
lemma exists_generic_spanning_of_isSimple (hS : P.IsSimple) :
    ∃ y : ℝ, (∀ i, (toReal (P.vert i)).2 ≠ y) ∧ (P.spanningSet y).Nonempty := by
  classical
  obtain ⟨m, hlex⟩ := exists_lex_lowest_vertex P
  obtain ⟨y, hlo, hhi, hgen⟩ :=
    exists_generic_height_mem_Ioo P (toReal (P.vert m)).2 ((toReal (P.vert m)).2 + 1)
      (by linarith)
  refine ⟨y, hgen, ?_⟩
  have hccne := cornerCross_ne_zero_lex_lowest P hS m hlex
  by_cases hmp : (toReal (P.vert (m + 1))).2 = (toReal (P.vert m)).2
  · -- `m+1` at the minimum height ⟹ `m-1` strictly above ⟹ edge `m-1` spans
    refine ⟨m - 1, ?_⟩
    rw [spanning_at_lowest_band P m hlex y hlo hhi (m - 1)]
    right
    refine ⟨by rw [sub_add_cancel], ?_⟩
    intro hb
    apply hccne
    rw [cornerCross_eq_neg_cross_neighbors]
    have hp2 : (toReal (P.vert (m - 1)) - toReal (P.vert m)).2 = 0 := by
      simp only [Prod.snd_sub, hb, sub_self]
    have hq2 : (toReal (P.vert (m + 1)) - toReal (P.vert m)).2 = 0 := by
      simp only [Prod.snd_sub, hmp, sub_self]
    unfold cross
    rw [hp2, hq2]; ring
  · -- `m+1` strictly above ⟹ edge `m` spans
    refine ⟨m, ?_⟩
    rw [spanning_at_lowest_band P m hlex y hlo hhi m]
    exact Or.inl ⟨rfl, hmp⟩

/-- **`|winding| = 1` witness from a generic spanning height (orientation-free
core).** This is the body of `exists_abs_winding_eq_one` with the positive-orientation
input replaced by an explicit generic height `y` whose spanning set is nonempty.
Among the spanning edges pick the smallest-threshold one `a` (strict min by simplicity,
`crossThreshold_ne_distinct_spanning`) and place `xw` just right of `edgeThr y a` but
left of the second smallest threshold; then
`winding (xw, y) = (∑ spanning signs) − edgeSign y a = −edgeSign y a = ±1`. -/
lemma exists_abs_winding_eq_one_of_genericSpanning (hS : P.IsSimple)
    (y : ℝ) (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y) (hSne : (P.spanningSet y).Nonempty) :
    ∃ q : ℝ × ℝ, q ∉ P.boundary ∧ (P.winding q = 1 ∨ P.winding q = -1) := by
  classical
  -- smallest-threshold spanning edge `a`
  obtain ⟨a, haS, hamin⟩ := (P.spanningSet y).exists_min_image (P.edgeThr y) hSne
  have hspan_of_mem : ∀ i ∈ P.spanningSet y,
      ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) := by
    intro i hi; unfold LatticePolygon.spanningSet at hi
    exact (Finset.mem_filter.mp hi).2
  have hstrict : ∀ i ∈ P.spanningSet y, i ≠ a → P.edgeThr y a < P.edgeThr y i := by
    intro i hiS hia
    refine lt_of_le_of_ne (hamin i hiS) ?_
    have hne := crossThreshold_ne_distinct_spanning P hS y hgen a i (Ne.symm hia)
      (hspan_of_mem a haS) (hspan_of_mem i hiS)
    exact fun h => hne (by unfold LatticePolygon.edgeThr at h; exact h)
  have hSother_ne : ((P.spanningSet y).erase a).Nonempty := by
    rcases ((P.spanningSet y).erase a).eq_empty_or_nonempty with hE | hN
    · exfalso
      have hsingle : P.spanningSet y = {a} := by
        rw [← Finset.insert_erase haS, hE]; rfl
      have hsum : ∑ i ∈ P.spanningSet y, P.edgeSign y i = 0 :=
        sum_edgeSign_spanning_eq_zero P y hgen
      rw [hsingle, Finset.sum_singleton] at hsum
      rcases edgeSign_eq_one_or_neg_one P y a with h | h <;> rw [h] at hsum <;>
        exact absurd hsum (by norm_num)
    · exact hN
  obtain ⟨c, hcS, hcmin⟩ := ((P.spanningSet y).erase a).exists_min_image (P.edgeThr y) hSother_ne
  have hcmem : c ∈ P.spanningSet y := (Finset.mem_erase.mp hcS).2
  have hcne : c ≠ a := (Finset.mem_erase.mp hcS).1
  have hclt : P.edgeThr y a < P.edgeThr y c := hstrict c hcmem hcne
  set xw := (P.edgeThr y a + P.edgeThr y c) / 2 with hxw
  have hxwL : P.edgeThr y a < xw := by rw [hxw]; linarith
  have hxwR : ∀ i ∈ P.spanningSet y, i ≠ a → xw < P.edgeThr y i := by
    intro i hiS hine
    have : P.edgeThr y c ≤ P.edgeThr y i := hcmin i (Finset.mem_erase.mpr ⟨hine, hiS⟩)
    rw [hxw]; linarith
  refine ⟨(xw, y), ?_, ?_⟩
  · intro hb
    obtain ⟨i, hiS, hxeq⟩ := exists_spanning_threshold_of_mem_boundary P y hgen xw hb
    by_cases hia : i = a
    · rw [hia] at hxeq; rw [hxeq] at hxwL; exact lt_irrefl _ hxwL
    · have := hxwR i hiS hia; rw [hxeq] at this; exact lt_irrefl _ this
  · rw [winding_eq_sum_spanning P xw y hgen]
    have hset : (P.spanningSet y).filter (fun i => xw < P.edgeThr y i)
        = (P.spanningSet y).erase a := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hiS, hlt⟩
        exact ⟨by rintro rfl; exact absurd hxwL (not_lt.mpr (le_of_lt hlt)), hiS⟩
      · rintro ⟨hne, hiS⟩; exact ⟨hiS, hxwR i hiS hne⟩
    rw [hset, Finset.sum_erase_eq_sub haS, sum_edgeSign_spanning_eq_zero P y hgen]
    rcases edgeSign_eq_one_or_neg_one P y a with h | h <;> rw [h]
    · right; ring
    · left; ring

/-- **`|winding| = 1` witness (orientation-free).** Every simple polygon has an
off-boundary point with `winding = ±1`. Combine `exists_generic_spanning_of_isSimple`
with `exists_abs_winding_eq_one_of_genericSpanning`. -/
lemma exists_abs_winding_eq_one_of_isSimple (hsimple : P.IsSimple) :
    ∃ q : ℝ × ℝ, q ∉ P.boundary ∧ (P.winding q = 1 ∨ P.winding q = -1) := by
  obtain ⟨y, hgen, hSne⟩ := exists_generic_spanning_of_isSimple P hsimple
  exact exists_abs_winding_eq_one_of_genericSpanning P hsimple y hgen hSne

/-- **Off-boundary winding is `{0, v}`-valued (orientation-free).** Same as
`winding_mem_zero_or_witness` but with the orientation-dependent witness replaced by
the orientation-free `exists_abs_winding_eq_one_of_isSimple`. The two-piece
decomposition `compl_boundary_atMost_two` (with `winding` constant on each piece) and
the far-field zero `exists_offBoundary_winding_zero` are already orientation-free. -/
lemma winding_mem_zero_or_witness_of_isSimple (hsimple : P.IsSimple) :
    ∃ v : ℤ, (v = 1 ∨ v = -1) ∧ ∀ q : ℝ × ℝ, q ∉ P.boundary →
      P.winding q = 0 ∨ P.winding q = v := by
  classical
  obtain ⟨A, B, hAB, hApre, hBpre⟩ := compl_boundary_atMost_two P hsimple
  obtain ⟨q0, hq0b, hq0w⟩ := exists_offBoundary_winding_zero P hsimple
  obtain ⟨w, hwb, hwabs⟩ := exists_abs_winding_eq_one_of_isSimple P hsimple
  set v := P.winding w with hv
  refine ⟨v, hwabs, ?_⟩
  have hAsub : A ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_left
  have hBsub : B ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_right
  have hq0mem : q0 ∈ A ∪ B := by rw [hAB]; exact hq0b
  have hwmem : w ∈ A ∪ B := by rw [hAB]; exact hwb
  have hconstA : ∀ x ∈ A, ∀ y ∈ A, P.winding x = P.winding y := fun x hx y hy =>
    winding_const_of_isPreconnected P hAsub hApre hx hy
  have hconstB : ∀ x ∈ B, ∀ y ∈ B, P.winding x = P.winding y := fun x hx y hy =>
    winding_const_of_isPreconnected P hBsub hBpre hx hy
  have hv01 : v = 1 ∨ v = -1 := hwabs
  have hvne : v ≠ 0 := by rcases hv01 with h | h <;> rw [h] <;> decide
  intro q hqb
  have hqmem : q ∈ A ∪ B := by rw [hAB]; exact hqb
  rcases hqmem with hqA | hqB <;> rcases hq0mem with h0A | h0B <;>
    rcases hwmem with hwA | hwB
  · left; rw [hconstA q hqA q0 h0A]; exact hq0w
  · left; rw [hconstA q hqA q0 h0A]; exact hq0w
  · right; rw [hconstA q hqA w hwA]
  · exfalso
    have : P.winding w = P.winding q0 := hconstB w hwB q0 h0B
    rw [hq0w] at this; exact hvne this
  · exfalso
    have : P.winding w = P.winding q0 := hconstA w hwA q0 h0A
    rw [hq0w] at this; exact hvne this
  · right; rw [hconstB q hqB w hwB]
  · left; rw [hconstB q hqB q0 h0B]; exact hq0w
  · left; rw [hconstB q hqB q0 h0B]; exact hq0w

/-- **A simple polygon has nonzero signed area** (`P.IsSimple → P.shoelace ≠ 0`),
orientation-free. By Green `shoelace = ∫ winding`; off the null boundary
`winding ∈ {0, v}` with `v = ±1` (`winding_mem_zero_or_witness_of_isSimple`), so
`∫ winding = v · volume {winding = v}`. The witness set `{winding = v}` contains a
neighbourhood of the `|winding| = 1` point (winding is locally constant off the
boundary, `winding_eventually_eq_full`), hence has positive volume; thus
`|shoelace| = volume {winding = v} > 0`. -/
lemma shoelace_ne_zero_of_isSimple (hsimple : P.IsSimple) : P.shoelace ≠ 0 := by
  classical
  obtain ⟨v, hv01, hmem⟩ := winding_mem_zero_or_witness_of_isSimple P hsimple
  obtain ⟨w, hwb, hwabs⟩ := exists_abs_winding_eq_one_of_isSimple P hsimple
  have hvne : v ≠ 0 := by rcases hv01 with h | h <;> rw [h] <;> decide
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hvne
  -- the witness has winding `= v`
  have hwv : P.winding w = v := by
    rcases hmem w hwb with h0 | hvw
    · exfalso; rcases hwabs with h1 | h1 <;> rw [h1] at h0 <;> norm_num at h0
    · exact hvw
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | P.winding q = v} with hS
  have hSmeas : MeasurableSet S := measurable_winding P (measurableSet_singleton v)
  have hSsub : S ⊆ {q : ℝ × ℝ | P.winding q ≠ 0} := by
    intro q hq; simp only [hS, Set.mem_setOf_eq] at hq ⊢; rw [hq]; exact hvne
  have hSfin : MeasureTheory.volume S ≠ ⊤ :=
    ne_top_of_le_ne_top (windingSupport_volume_ne_top P) (MeasureTheory.measure_mono hSsub)
  -- `winding =ᵐ v · indicator S`
  have hbnull : P.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero P hsimple
  have heq : (fun q => (P.winding q : ℝ))
      =ᵐ[MeasureTheory.volume] (fun q => (v : ℝ) * S.indicator (fun _ => (1 : ℝ)) q) := by
    filter_upwards [hbnull] with q hq
    rcases hmem q hq with h0 | hvq
    · have hnotS : q ∉ S := fun hc => hvne (by
        rw [hS, Set.mem_setOf_eq, h0] at hc; exact hc.symm)
      rw [Set.indicator_of_notMem hnotS, mul_zero, h0]; norm_num
    · have hinS : q ∈ S := by rw [hS, Set.mem_setOf_eq]; exact hvq
      rw [Set.indicator_of_mem hinS, mul_one, hvq]
  -- the witness set has positive volume (it contains a neighbourhood of `w`)
  have hSnhds : S ∈ nhds w := by
    have hev := winding_eventually_eq_full P w hwb
    rw [hwv] at hev; exact hev
  obtain ⟨U, hUS, hUopen, hwU⟩ := _root_.mem_nhds_iff.mp hSnhds
  have hpos : (0 : ENNReal) < MeasureTheory.volume S :=
    lt_of_lt_of_le (hUopen.measure_pos MeasureTheory.volume ⟨w, hwU⟩)
      (MeasureTheory.measure_mono hUS)
  have htoRpos : 0 < (MeasureTheory.volume S).toReal := ENNReal.toReal_pos (ne_of_gt hpos) hSfin
  -- `shoelace = v · volume S`
  have hint : (∫ q, (P.winding q : ℝ)) = (v : ℝ) * (MeasureTheory.volume S).toReal := by
    rw [MeasureTheory.integral_congr_ae heq, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator_const (1 : ℝ) hSmeas, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]
  have hshoe : P.shoelace = (v : ℝ) * (MeasureTheory.volume S).toReal := by
    rw [← greens_theorem P]; exact hint
  rw [hshoe]
  exact mul_ne_zero hvR (ne_of_gt htoRpos)

/-- **Orientation-free `|shoelace| = filled volume`.** For a simple polygon the absolute
signed area equals the Lebesgue measure of the *filled* region `{winding ≠ 0}` (the witness
set `{winding = v}`, which only differs from `{winding ≠ 0}` on the null boundary). This is
the orientation-free quantity that adds across a diagonal split. -/
lemma abs_shoelace_eq_filledMeasure (hsimple : P.IsSimple) :
    |P.shoelace| = (MeasureTheory.volume {q : ℝ × ℝ | P.winding q ≠ 0}).toReal := by
  classical
  obtain ⟨v, hv01, hmem⟩ := winding_mem_zero_or_witness_of_isSimple P hsimple
  have hvne : v ≠ 0 := by rcases hv01 with h | h <;> rw [h] <;> decide
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | P.winding q = v} with hS
  have hSmeas : MeasurableSet S := measurable_winding P (measurableSet_singleton v)
  have hSsub : S ⊆ {q : ℝ × ℝ | P.winding q ≠ 0} := by
    intro q hq; simp only [hS, Set.mem_setOf_eq] at hq ⊢; rw [hq]; exact hvne
  have hbnull : P.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero P hsimple
  have heq : (fun q => (P.winding q : ℝ))
      =ᵐ[MeasureTheory.volume] (fun q => (v : ℝ) * S.indicator (fun _ => (1 : ℝ)) q) := by
    filter_upwards [hbnull] with q hq
    rcases hmem q hq with h0 | hvq
    · have hnotS : q ∉ S := fun hc => hvne (by
        rw [hS, Set.mem_setOf_eq, h0] at hc; exact hc.symm)
      rw [Set.indicator_of_notMem hnotS, mul_zero, h0]; norm_num
    · have hinS : q ∈ S := by rw [hS, Set.mem_setOf_eq]; exact hvq
      rw [Set.indicator_of_mem hinS, mul_one, hvq]
  have hint : (∫ q, (P.winding q : ℝ)) = (v : ℝ) * (MeasureTheory.volume S).toReal := by
    rw [MeasureTheory.integral_congr_ae heq, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator_const (1 : ℝ) hSmeas, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]
  have hshoe : P.shoelace = (v : ℝ) * (MeasureTheory.volume S).toReal := by
    rw [← greens_theorem P]; exact hint
  have habsv : |(v : ℝ)| = 1 := by rcases hv01 with h | h <;> rw [h] <;> norm_num
  have hL : |P.shoelace| = (MeasureTheory.volume S).toReal := by
    rw [hshoe, abs_mul, habsv, one_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have hae : S =ᵐ[MeasureTheory.volume] {q : ℝ × ℝ | P.winding q ≠ 0} := by
    filter_upwards [hbnull] with q hq
    have hiff : (q ∈ S) ↔ (q ∈ {q : ℝ × ℝ | P.winding q ≠ 0}) := by
      simp only [hS, Set.mem_setOf_eq]
      constructor
      · intro h; rw [h]; exact hvne
      · intro h; rcases hmem q hq with h0 | hv
        · exact absurd h0 h
        · exact hv
    exact propext hiff
  rw [hL, MeasureTheory.measure_congr hae]

/-- **`h01_ae` for general simple positively-oriented polygons.** Almost every point
has winding `0` or `1`. The boundary is null (`volume_boundary_eq_zero`); off it,
`winding_mem_zero_or_witness` gives winding `∈ {0, v}` with `v = ±1`, and `v = 1` is
forced because `∫ winding = shoelace > 0` (`winding_integral_pos`) rules out `v = -1`. -/
theorem h01_ae (hsimple : P.IsSimple) (horient : P.PositivelyOriented) :
    ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = 1 := by
  obtain ⟨v, hv01, hmem⟩ := winding_mem_zero_or_witness P hsimple horient
  have hbnull : P.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero P hsimple
  have hae0v : ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = v := by
    filter_upwards [hbnull] with q hq
    exact hmem q hq
  -- exclude v = -1 via positive total integral
  have hvpos : v = 1 := by
    rcases hv01 with h1 | hm1
    · exact h1
    · exfalso
      have hle : ∀ᵐ q : ℝ × ℝ, (P.winding q : ℝ) ≤ 0 := by
        filter_upwards [hae0v] with q hq
        rcases hq with h | h
        · rw [h]; norm_num
        · rw [h, hm1]; norm_num
      have hint_le : (∫ q, (P.winding q : ℝ)) ≤ 0 :=
        MeasureTheory.integral_nonpos_of_ae hle
      exact absurd hint_le (not_le.mpr (winding_integral_pos P horient))
  rw [hvpos] at hae0v
  exact hae0v

/-- **The winding bound `winding_zero_or_one`.** For a simple, positively-oriented
lattice polygon, every off-boundary point has winding `0` or `1`. This is the
(non-circular) topological unlock for Pick's theorem. -/
theorem winding_zero_or_one (hsimple : P.IsSimple) (horient : P.PositivelyOriented) :
    ∀ q : ℝ × ℝ, q ∉ P.boundary → P.winding q = 0 ∨ P.winding q = 1 := by
  obtain ⟨v, hv01, hmem⟩ := winding_mem_zero_or_witness P hsimple horient
  -- pin v = 1 by Green, exactly as in `h01_ae`
  have hbnull : P.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero P hsimple
  have hae0v : ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = v := by
    filter_upwards [hbnull] with q hq; exact hmem q hq
  have hvpos : v = 1 := by
    rcases hv01 with h1 | hm1
    · exact h1
    · exfalso
      have hle : ∀ᵐ q : ℝ × ℝ, (P.winding q : ℝ) ≤ 0 := by
        filter_upwards [hae0v] with q hq
        rcases hq with h | h
        · rw [h]; norm_num
        · rw [h, hm1]; norm_num
      have hint_le : (∫ q, (P.winding q : ℝ)) ≤ 0 :=
        MeasureTheory.integral_nonpos_of_ae hle
      exact absurd hint_le (not_le.mpr (winding_integral_pos P horient))
  intro q hqb
  rcases hmem q hqb with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h, hvpos])

/-- **Lowest-band cross-section nonneg from `winding_zero_or_one`** (non-circular).
At a generic height `y`, the cross-section `∫ x, winding(x, y)` is `≥ 0`: off the
finite line-boundary, `winding (x, y) ∈ {0, 1}` (`winding_zero_or_one`), so the
integrand is a.e. nonnegative. -/
theorem crossSection_nonneg (hsimple : P.IsSimple) (horient : P.PositivelyOriented)
    (y : ℝ) (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    0 ≤ ∫ x, (P.winding (x, y) : ℝ) := by
  have hfin := lineBoundary_finite P y hgen
  have hae : ∀ᵐ x ∂MeasureTheory.volume, 0 ≤ (P.winding (x, y) : ℝ) := by
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ (hfin.measure_zero MeasureTheory.volume)
    intro x hx
    simp only [Set.mem_setOf_eq, not_le] at hx
    by_contra hxb
    rcases winding_zero_or_one P hsimple horient (x, y) hxb with h | h <;>
      rw [h] at hx <;> norm_num at hx
  exact MeasureTheory.integral_nonneg_of_ae hae

/-- **Lowest-vertex corner is convex** (FINALLY non-circular, via `winding_zero_or_one`).
For a simple, positively-oriented polygon whose lex-lowest vertex `m` is the *unique*
minimum-height vertex with both neighbours strictly above it, the corner at `m` is a
strict left turn: `0 < cornerCross P m`. Proof: at a generic height `y` in the lowest
unit band, the cross-section `∫ winding(·, y)` equals the signed threshold gap
`edgeThr y m − edgeThr y (m−1)` (`crossSection_unique_lowest`) and is `≥ 0`
(`crossSection_nonneg`, from `winding_zero_or_one`), so the gap is `≥ 0`, giving
`0 ≤ cornerCross P m`; the strict third simplicity clause
(`cornerCross_pos_of_weak`) upgrades it to `0 < cornerCross P m`. This discharges the
former `FanSignWeak` input at the (unique) lowest vertex with no circular
orientation/Hopf assumption. -/
theorem cornerCross_pos_lex_lowest_winding (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (huniq : ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert m)).2 → j = m)
    (hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2)
    (hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2) :
    0 < cornerCross P m := by
  -- choose a generic height in the lowest unit band
  obtain ⟨y, hlo, hhi, hgen⟩ :=
    exists_generic_height_mem_Ioo P (toReal (P.vert m)).2 ((toReal (P.vert m)).2 + 1)
      (by linarith)
  -- the cross-section equals the signed threshold gap and is nonnegative
  have hcs := crossSection_unique_lowest P m hlex huniq hba hbc y hlo hhi hgen
  have hnn := crossSection_nonneg P hS hO y hgen
  rw [hcs] at hnn
  have hthr : P.edgeThr y (m - 1) ≤ P.edgeThr y m := by linarith
  -- nonneg gap ⟹ nonneg corner cross (sign transfer via `crossThreshold_gap_eq_cornerCross`)
  have hweak : 0 ≤ cornerCross P m := by
    have hcorner : cornerCross P m =
        cross (toReal (P.vert m) - toReal (P.vert (m - 1)))
              (toReal (P.vert (m + 1)) - toReal (P.vert m)) := by
      unfold cornerCross; rfl
    have hkey := crossThreshold_gap_eq_cornerCross
      (toReal (P.vert (m - 1))) (toReal (P.vert m)) (toReal (P.vert (m + 1))) y hba hbc hlo
    have hedge1 : P.edgeThr y (m - 1) =
        crossThreshold (toReal (P.vert (m - 1))) (toReal (P.vert m)) y := by
      unfold LatticePolygon.edgeThr; rw [sub_add_cancel]
    have hedge2 : P.edgeThr y m =
        crossThreshold (toReal (P.vert m)) (toReal (P.vert (m + 1))) y := by
      unfold LatticePolygon.edgeThr; rfl
    rw [hedge1, hedge2] at hthr
    have hprod : 0 ≤ ((toReal (P.vert (m - 1))).2 - (toReal (P.vert m)).2) *
        ((toReal (P.vert (m + 1))).2 - (toReal (P.vert m)).2) := by
      apply mul_nonneg <;> linarith
    have hgap : 0 ≤ crossThreshold (toReal (P.vert m)) (toReal (P.vert (m + 1))) y
        - crossThreshold (toReal (P.vert (m - 1))) (toReal (P.vert m)) y := by linarith
    have hrhs : 0 ≤ cornerCross P m * (y - (toReal (P.vert m)).2) := by
      rw [hcorner, ← hkey]; exact mul_nonneg hgap hprod
    have hy : 0 < y - (toReal (P.vert m)).2 := by linarith
    exact nonneg_of_mul_nonneg_left hrhs hy
  exact cornerCross_pos_of_weak P hS m hlex hweak

/-- **Ear/clip winding disjointness off `R`'s boundary** (FINALLY non-circular, via
`winding_zero_or_one`). For a simple, positively-oriented `R`, at any point off
`R.boundary` the clip `deleteLast R` and the ear triangle `earTri R` never both have
winding `1`: by additivity `R.winding q = (deleteLast R).winding q + (earTri R).winding q`
and `winding_zero_or_one R` pins `R.winding q ∈ {0,1}`, so both summands `= 1` would
force `R.winding q = 2 ∉ {0,1}`. This is conjunct 5 of `ValidEarLast` restricted to
off-boundary points — the only place the disjointness is consumed (`h01_of_split`
applies it inside an a.e. filter), with the genuine former-circular content
discharged. The remaining `∀ q` (boundary) closure needs a global `winding ≤ 1`
crossing bound, not the measure-level `winding_zero_or_one`. -/
theorem earTri_disjoint_winding_offBoundary (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (h2 : 2 ≤ P.n) (m : ℕ) (hm : P.n = m + 2) (q : ℝ × ℝ) (hqb : q ∉ P.boundary) :
    ¬((deleteLast P h2).winding q = 1 ∧ (earTri P m hm).winding q = 1) := by
  rintro ⟨h1, h1'⟩
  have hadd := winding_eq_deleteLast_add_earTri P h2 m hm q
  rw [h1, h1'] at hadd
  -- hadd : R.winding q = 2
  rcases winding_zero_or_one P hS hO q hqb with h | h <;> rw [h] at hadd <;>
    exact absurd hadd (by norm_num)

/-! ### Conjunct 6 scaffolding: interior-lattice partition across the diagonal

For a simple positively-oriented `R` with `R.n = m+2`, deleting the last vertex splits
the interior into the clip `deleteLast R`, the ear triangle `earTri R`, and the open
diagonal `vₘ → v₀`. We build the `I`/`B` additivity from winding additivity plus the
off-boundary disjointness. -/

/-- The **open diagonal** of the clip: the diagonal segment `vₘ → v₀` minus `R.boundary`
(equivalently, minus its two endpoints, which lie on `R.boundary`). A lattice point on
the open diagonal lies on both `(deleteLast R).boundary` and `(earTri R).boundary` but
off `R.boundary`. -/
lemma diag_subset_deleteLast_boundary (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) :
    segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
      ⊆ (deleteLast R h2).boundary := by
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  intro x hx
  refine Set.mem_iUnion.2 ⟨((m : ℕ) : ZMod (deleteLast R h2).n), ?_⟩
  have hmval : (((m : ℕ) : ZMod (deleteLast R h2).n)).val = m := by
    rw [ZMod.val_natCast, hn1, Nat.mod_eq_of_lt (by omega)]
  rw [deleteLast_edgeSeg_diag R h2 m hm _ hmval]
  exact hx

/-- The diagonal `vₘ → v₀` is contained in the ear triangle's boundary. -/
lemma diag_subset_earTri_boundary (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2) :
    segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
      ⊆ (earTri R m hm).boundary := by
  intro x hx
  refine Set.mem_iUnion.2 ⟨2, ?_⟩
  have hv2 : (earTri R m hm).vert 2 = R.vert 0 := rfl
  have hv3 : (earTri R m hm).vert (2 + 1) = R.vert (m : ZMod R.n) := rfl
  rw [LatticePolygon.edgeSeg, hv2, hv3, segment_symm]; exact hx

/-- **Off-diagonal points are off both pieces' boundaries.** A point off `R.boundary`
and off the diagonal `vₘ → v₀` lies off both `(deleteLast R).boundary` and
`(earTri R).boundary`. Immediate from `boundary_deleteLast_union_earTri`. -/
lemma offDiag_off_pieces (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2)
    (x : ℝ × ℝ) (hxR : x ∉ R.boundary)
    (hxd : x ∉ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))) :
    x ∉ (deleteLast R h2).boundary ∧ x ∉ (earTri R m hm).boundary := by
  have hun := boundary_deleteLast_union_earTri R h2 m hm
  have hxU : x ∉ (deleteLast R h2).boundary ∪ (earTri R m hm).boundary := by
    rw [hun]; intro hc; rcases hc with h | h; exacts [hxR h, hxd h]
  exact ⟨fun h => hxU (Or.inl h), fun h => hxU (Or.inr h)⟩

/-- **Interior-lattice membership across the diagonal (off-diagonal points).** For a
simple positively-oriented `R`, with each piece's winding pinned to `{0,1}` off its own
boundary (`hdL01`, `hear01`), a lattice point `q` off `R.boundary` and off the
diagonal lies in `interiorLattice R` iff it lies in exactly one of the two pieces'
interior lattices. The `winding ∈ {0,1}` dichotomy plus additivity make the
membership an exclusive-or. -/
lemma interiorLattice_mem_offDiag (R : LatticePolygon) (_ : R.IsSimple)
    (_ : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2)
    (hdL01 : ∀ p, p ∉ (deleteLast R h2).boundary →
      (deleteLast R h2).winding p = 0 ∨ (deleteLast R h2).winding p = 1)
    (hear01 : ∀ p, p ∉ (earTri R m hm).boundary →
      (earTri R m hm).winding p = 0 ∨ (earTri R m hm).winding p = 1)
    (q : Pt) (hxR : toReal q ∉ R.boundary)
    (hxd : toReal q ∉ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))) :
    (q ∈ R.interiorLattice) ↔
      (q ∈ (deleteLast R h2).interiorLattice ∧ q ∉ (earTri R m hm).interiorLattice) ∨
      (q ∉ (deleteLast R h2).interiorLattice ∧ q ∈ (earTri R m hm).interiorLattice) := by
  obtain ⟨hdLb, hearb⟩ := offDiag_off_pieces R h2 m hm (toReal q) hxR hxd
  have hadd := winding_eq_deleteLast_add_earTri R h2 m hm (toReal q)
  have hd := hdL01 (toReal q) hdLb
  have he := hear01 (toReal q) hearb
  simp only [LatticePolygon.interiorLattice, Set.mem_setOf_eq]
  constructor
  · intro hR
    have hR1 : R.winding (toReal q) = 1 := hR.1
    rw [hadd] at hR1
    rcases hd with hd0 | hd1 <;> rcases he with he0 | he1
    · omega
    · exact Or.inr ⟨fun hc => by rw [hc.1] at hd0; omega, ⟨he1, hearb⟩⟩
    · exact Or.inl ⟨⟨hd1, hdLb⟩, fun hc => by rw [hc.1] at he0; omega⟩
    · omega
  · intro hpieces
    refine ⟨?_, hxR⟩
    rw [hadd]
    rcases hpieces with ⟨⟨hdw, _⟩, hearnot⟩ | ⟨hdLnot, ⟨hew, _⟩⟩
    · rcases he with he0 | he1
      · rw [hdw, he0]; norm_num
      · exact absurd ⟨he1, hearb⟩ hearnot
    · rcases hd with hd0 | hd1
      · rw [hd0, hew]; norm_num
      · exact absurd ⟨hd1, hdLb⟩ hdLnot

/-! ### Conjunct 6: the `I`/`B` lattice-count additivity (`hIB`)

We assemble the exact `ValidEarLast` conjunct
`R.I + R.B/2 = clip.I + ear.I + (clip.B + ear.B)/2 − 1`
from two combinatorial identities, where `d` is the number of lattice points on the
**open** diagonal `vₘ → v₀`:
  * `R.I = clip.I + ear.I + d`           (interior partition across the diagonal)
  * `clip.B + ear.B = R.B + 2d + 2`      (boundary inclusion–exclusion on the diagonal).
-/

/-- The **closed-diagonal lattice points**: lattice points on the closed diagonal segment
`vₘ → v₀` (the clip's new edge / the ear's hypotenuse). -/
def diagLattice (R : LatticePolygon) (m : ℕ) : Set Pt :=
  {q : Pt | toReal q ∈ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))}

/-- The closed diagonal lattice is contained in the clip's boundary lattice (the diagonal
is an edge of `deleteLast R`). -/
lemma diagLattice_subset_deleteLast_boundaryLattice (R : LatticePolygon) (h2 : 2 ≤ R.n)
    (m : ℕ) (hm : R.n = m + 2) :
    diagLattice R m ⊆ (deleteLast R h2).boundaryLattice := by
  intro q hq
  exact diag_subset_deleteLast_boundary R h2 m hm hq

/-- The closed diagonal lattice is contained in the ear's boundary lattice. -/
lemma diagLattice_subset_earTri_boundaryLattice (R : LatticePolygon) (m : ℕ)
    (hm : R.n = m + 2) :
    diagLattice R m ⊆ (earTri R m hm).boundaryLattice := by
  intro q hq
  exact diag_subset_earTri_boundary R m hm hq

/-- The closed-diagonal lattice set is finite. -/
lemma diagLattice_finite (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) :
    (diagLattice R m).Finite :=
  (boundaryLattice_finite (deleteLast R h2)).subset
    (diagLattice_subset_deleteLast_boundaryLattice R h2 m hm)

/-- The two diagonal endpoints `vₘ, v₀` are distinct lattice points (from ear simplicity:
the ear triangle's third edge `v₀ → vₘ` is non-degenerate). -/
lemma diag_endpoints_ne (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2)
    (hearS : (earTri R m hm).IsSimple) :
    R.vert (m : ZMod R.n) ≠ R.vert 0 := by
  have h := hearS.1 2
  -- earTri.vert 2 = R.vert 0, earTri.vert (2+1) = earTri.vert 0 = R.vert m
  have e1 : (earTri R m hm).vert 2 = R.vert 0 := rfl
  have e2 : (earTri R m hm).vert (2 + 1) = R.vert (m : ZMod R.n) := rfl
  rw [e1, e2] at h
  exact fun hc => h hc.symm

/-- The two endpoints lie in the closed-diagonal lattice. -/
lemma diag_endpoint_m_mem (R : LatticePolygon) (m : ℕ) :
    R.vert (m : ZMod R.n) ∈ diagLattice R m :=
  left_mem_segment ℝ _ _

lemma diag_endpoint_0_mem (R : LatticePolygon) (m : ℕ) :
    R.vert 0 ∈ diagLattice R m :=
  right_mem_segment ℝ _ _

/-- The two endpoints lie in `R`'s boundary lattice. -/
lemma diag_endpoint_m_mem_R_bdry (R : LatticePolygon) (m : ℕ) :
    R.vert (m : ZMod R.n) ∈ R.boundaryLattice :=
  vert_mem_boundaryLattice R _

lemma diag_endpoint_0_mem_R_bdry (R : LatticePolygon) (_ : ℕ) :
    R.vert 0 ∈ R.boundaryLattice :=
  vert_mem_boundaryLattice R 0

/-- **Clip and ear interiors are disjoint.** If a lattice point were interior to both
the clip and the ear, then `R.winding = clip.winding + ear.winding = 2`; but the point
is off both pieces' boundaries hence off `R.boundary` (the diagonal lies in both), so
`winding_zero_or_one R` forbids `R.winding = 2`. -/
lemma deleteLast_earTri_interiorLattice_disjoint (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) :
    Disjoint (deleteLast R h2).interiorLattice (earTri R m hm).interiorLattice := by
  rw [Set.disjoint_left]
  intro q hqd hqe
  have hdLb : toReal q ∉ (deleteLast R h2).boundary := hqd.2
  have hearb : toReal q ∉ (earTri R m hm).boundary := hqe.2
  have hxR : toReal q ∉ R.boundary := by
    intro hRb
    have hun := boundary_deleteLast_union_earTri R h2 m hm
    have : toReal q ∈ (deleteLast R h2).boundary ∪ (earTri R m hm).boundary := by
      rw [hun]; exact Or.inl hRb
    rcases this with h | h
    exacts [hdLb h, hearb h]
  have hadd := winding_eq_deleteLast_add_earTri R h2 m hm (toReal q)
  rw [hqd.1, hqe.1] at hadd
  rcases winding_zero_or_one R hS hO (toReal q) hxR with hr | hr <;>
    rw [hr] at hadd <;> norm_num at hadd

/-- **Lattice version of the boundary union.** Lifting `boundary_deleteLast_union_earTri`
to lattice points: `clip.B ∪ ear.B = R.B ∪ diagLattice` as subsets of `Pt`. Free (no
geometry), just unfolding `boundaryLattice` and pulling back the real-set equality. -/
lemma boundaryLattice_deleteLast_union_earTri (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) :
    (deleteLast R h2).boundaryLattice ∪ (earTri R m hm).boundaryLattice
      = R.boundaryLattice ∪ diagLattice R m := by
  have hun := boundary_deleteLast_union_earTri R h2 m hm
  ext q
  simp only [LatticePolygon.boundaryLattice, diagLattice, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · have : toReal q ∈ R.boundary ∪ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := by
        rw [← hun]; exact Or.inl h
      exact this
    · have : toReal q ∈ R.boundary ∪ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := by
        rw [← hun]; exact Or.inr h
      exact this
  · intro h
    have : toReal q ∈ (deleteLast R h2).boundary ∪ (earTri R m hm).boundary := by
      rw [hun]; exact h
    exact this

/-- **The diagonal endpoints, as a two-element set.** `{vₘ, v₀}` has exactly two elements. -/
lemma diag_endpoints_ncard (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2)
    (hearS : (earTri R m hm).IsSimple) :
    ({R.vert (m : ZMod R.n), R.vert 0} : Set Pt).ncard = 2 := by
  rw [Set.ncard_pair (diag_endpoints_ne R m hm hearS)]

/-- **`hP3` from `hDisj` for an empty ear.** A lattice point on both `R`'s boundary and
the closed diagonal `[vₘ, v₀]` is one of the two endpoints `vₘ`, `v₀`. The point lies on
some edge `R.edgeSeg k`; if `k` is non-incident (`≠ m−1, m, 0`) then `hDisj` makes the
diagonal disjoint from it (impossible). The three incident edges meet the diagonal only at
the endpoints: edges `m−1`, `0` by the two turn lemmas (`diag_adjPrev_inter`,
`diag_adjNext_inter`), and edge `m` by non-collinearity at `vₘ` (`earTri_cross_base_pos`). -/
lemma hP3_of_emptyEar (R : LatticePolygon) (hS : R.IsSimple) (m : ℕ) (hm : R.n = m + 2)
    (hm2 : 2 ≤ m) (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    R.boundaryLattice ∩ diagLattice R m
      ⊆ {R.vert (m : ZMod R.n), R.vert 0} := by
  classical
  have hbase := earTri_cross_base_pos R m hm hear
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  -- m-1 (as ZMod) successor identity
  have hm0 : ((m - 1 : ℕ) : ZMod R.n) + 1 = (m : ZMod R.n) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  rintro q ⟨hqb, hqd⟩
  -- q is on some edge k of R
  simp only [LatticePolygon.boundaryLattice, LatticePolygon.boundary, Set.mem_setOf_eq,
    Set.mem_iUnion] at hqb
  obtain ⟨k, hk⟩ := hqb
  have hqD : toReal q ∈ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := hqd
  -- dichotomy on k vs the three incident indices
  by_cases hkm1 : k = (m : ZMod R.n) - 1
  · -- edge m-1 : intersection with D is {v_m}
    have hidx : ((m : ZMod R.n) - 1) = ((m - 1 : ℕ) : ZMod R.n) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hmem : toReal q ∈ segment ℝ (toReal (R.vert (((m - 1 : ℕ)) : ZMod R.n)))
        (toReal (R.vert (m : ZMod R.n)))
        ∩ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := by
      refine ⟨?_, hqD⟩
      rw [LatticePolygon.edgeSeg, hkm1, hidx, hm0] at hk; exact hk
    rw [diag_adjPrev_inter R hS m hm hm2 hear] at hmem
    left; exact toReal_injective hmem
  · by_cases hkm : k = (m : ZMod R.n)
    · -- edge m = [v_m, v_{m+1}]: meets D only at v_m (non-collinear, hbase)
      have hmp1 : (m : ZMod R.n) + 1 = (m : ZMod R.n) + 1 := rfl
      have hindep : segment ℝ (toReal (R.vert (m : ZMod R.n)))
            (toReal (R.vert ((m : ZMod R.n) + 1)))
          ∩ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
          = {toReal (R.vert (m : ZMod R.n))} := by
        apply segment_inter_eq_endpoint_of_linearIndependent_sub
        exact linearIndependent_of_cross_ne_zero _ _ (ne_of_gt hbase)
      have hmem : toReal q ∈ segment ℝ (toReal (R.vert (m : ZMod R.n)))
          (toReal (R.vert ((m : ZMod R.n) + 1)))
          ∩ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := by
        refine ⟨?_, hqD⟩
        rw [LatticePolygon.edgeSeg, hkm] at hk; exact hk
      rw [hindep] at hmem
      left; exact toReal_injective hmem
    · by_cases hkmp1 : k = (m : ZMod R.n) + 1
      · -- edge m+1 = [v_{m+1}, v_0]: meets D only at v_0 (shared endpoint, non-collinear)
        have hindep : segment ℝ (toReal (R.vert 0)) (toReal (R.vert (m : ZMod R.n)))
              ∩ segment ℝ (toReal (R.vert 0)) (toReal (R.vert ((m : ZMod R.n) + 1)))
            = {toReal (R.vert 0)} := by
          apply segment_inter_eq_endpoint_of_linearIndependent_sub
          refine linearIndependent_of_cross_ne_zero _ _ ?_
          -- cross (v_0 - v_m) (v_0 - v_{m+1}) equals the base area, hence ≠ 0
          have heq : cross (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0))
              (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert 0))
            = cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
                (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n))) := by
            simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
          rw [heq]; exact ne_of_gt hbase
        have hmem : toReal q ∈ segment ℝ (toReal (R.vert 0)) (toReal (R.vert (m : ZMod R.n)))
            ∩ segment ℝ (toReal (R.vert 0)) (toReal (R.vert ((m : ZMod R.n) + 1))) := by
          refine ⟨by rw [segment_symm]; exact hqD, ?_⟩
          rw [LatticePolygon.edgeSeg, hkmp1, hmp1mp1, segment_symm] at hk; exact hk
        rw [hindep] at hmem
        right; exact toReal_injective hmem
      · by_cases hk0 : k = 0
        · -- edge 0 = [v_0, v_1]: meets D only at v_0
          have hmem : toReal q ∈ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
              ∩ segment ℝ (toReal (R.vert 0)) (toReal (R.vert 1)) := by
            refine ⟨hqD, ?_⟩
            rw [LatticePolygon.edgeSeg, hk0, zero_add] at hk; exact hk
          rw [diag_adjNext_inter R hS m hm hm2 hear] at hmem
          right; exact toReal_injective hmem
        · -- non-incident edge : disjoint from D, contradiction
          exact absurd hk (Set.disjoint_left.mp
            (Pick.diag_disjoint_nonincident_edge R hS m hm hm2 hear k hkm1 hkm hkmp1 hk0) hqD)

/-- The ear triangle's boundary is the union of its three edges: the two legs
`[vₘ, vₘ₊₁]`, `[vₘ₊₁, v₀]` and the diagonal `[v₀, vₘ]`. -/
lemma earTri_boundary_eq (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2) :
    (earTri R m hm).boundary
      = segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert ((m : ZMod R.n) + 1)))
        ∪ segment ℝ (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0))
        ∪ segment ℝ (toReal (R.vert 0)) (toReal (R.vert (m : ZMod R.n))) := by
  rw [LatticePolygon.boundary]
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp only [LatticePolygon.edgeSeg, earTri] <;> intro y hy
    · exact Or.inl (Or.inl hy)
    · exact Or.inl (Or.inr hy)
    · exact Or.inr hy
  · intro y hy
    rcases hy with (hy | hy) | hy
    · exact Set.mem_iUnion.2 ⟨0, by
        simp only [LatticePolygon.edgeSeg, earTri]; exact hy⟩
    · exact Set.mem_iUnion.2 ⟨1, by
        simp only [LatticePolygon.edgeSeg, earTri]; exact hy⟩
    · exact Set.mem_iUnion.2 ⟨2, by
        simp only [LatticePolygon.edgeSeg, earTri]; exact hy⟩

/-- **`hP2` for an empty ear (Hopf-free).** The shared boundary lattice of the clip
`deleteLast R` and the ear triangle lies on the closed diagonal `[vₘ, v₀]`.  A shared
point is on some clip edge (a kept `R`-edge `↑j.val` with `j.val < m`, or the diagonal)
and on some ear edge (a leg `[vₘ, vₘ₊₁]`/`[vₘ₊₁, v₀]`, or the diagonal).  If either is
the diagonal we are done; otherwise a kept `R`-edge meets a leg only at the shared
triangle vertex `vₘ` or `v₀` (`R`-simplicity), both on the diagonal. -/
lemma hP2_of_emptyEar (R : LatticePolygon) (hS : R.IsSimple) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) (_ : 2 ≤ m) (_ : isEarVertex R ((m : ZMod R.n) + 1)) :
    (deleteLast R h2).boundaryLattice ∩ (earTri R m hm).boundaryLattice
      ⊆ diagLattice R m := by
  classical
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  rintro q ⟨hqc, hqe⟩
  rw [diagLattice, Set.mem_setOf_eq]
  have hqe' : toReal q ∈ (earTri R m hm).boundary := hqe
  rw [earTri_boundary_eq R m hm] at hqe'
  rcases hqe' with (hleg0 | hleg1) | hD
  · -- toReal q on leg_m = edgeSeg m = [v_m, v_{m+1}]
    have hqcm : toReal q ∈ R.edgeSeg (m : ZMod R.n) := by
      rw [LatticePolygon.edgeSeg]; exact hleg0
    simp only [LatticePolygon.boundaryLattice, LatticePolygon.boundary, Set.mem_setOf_eq,
      Set.mem_iUnion] at hqc
    obtain ⟨j, hj⟩ := hqc
    rcases deleteLast_idx_dichotomy R h2 m hm j with hjlt | hjeq
    · rw [deleteLast_edgeSeg_kept R h2 m hm j hjlt] at hj
      have hjval : ((((j.val : ℕ)) : ZMod R.n)).val = j.val := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      by_cases hjm1 : ((j.val : ℕ) : ZMod R.n) = (m : ZMod R.n) - 1
      · have hadj := hS.2.2 ((m : ZMod R.n) - 1)
        rw [show ((m : ZMod R.n) - 1) + 1 = (m : ZMod R.n) by ring] at hadj
        have hmem : toReal q ∈ R.edgeSeg ((m : ZMod R.n) - 1) ∩ R.edgeSeg (m : ZMod R.n) :=
          ⟨by rw [← hjm1]; exact hj, hqcm⟩
        rw [hadj, Set.mem_singleton_iff] at hmem
        rw [hmem]; exact left_mem_segment ℝ _ _
      · have hne : ((j.val : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) := by
          intro he; rw [he] at hjval
          have : ((m : ZMod R.n)).val = m := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          omega
        have hadj1 : ((j.val : ℕ) : ZMod R.n) + 1 ≠ (m : ZMod R.n) := by
          intro he; apply hjm1; linear_combination he
        have hadj2 : (m : ZMod R.n) + 1 ≠ ((j.val : ℕ) : ZMod R.n) := by
          intro he
          have hmp1v : (((m : ZMod R.n) + 1)).val = m + 1 := by
            rw [show (m : ZMod R.n) + 1 = (((m + 1 : ℕ)) : ZMod R.n) by push_cast; ring,
              ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          rw [← he, hmp1v] at hjval; omega
        exact (Set.disjoint_left.mp (hS.2.1 _ _ hne hadj1 hadj2) hj hqcm).elim
    · rw [deleteLast_edgeSeg_diag R h2 m hm j hjeq] at hj; exact hj
  · -- toReal q on leg_{m+1} = edgeSeg (m+1) = [v_{m+1}, v_0]
    have hqcm : toReal q ∈ R.edgeSeg ((m : ZMod R.n) + 1) := by
      rw [LatticePolygon.edgeSeg, hmp1mp1]; exact hleg1
    simp only [LatticePolygon.boundaryLattice, LatticePolygon.boundary, Set.mem_setOf_eq,
      Set.mem_iUnion] at hqc
    obtain ⟨j, hj⟩ := hqc
    rcases deleteLast_idx_dichotomy R h2 m hm j with hjlt | hjeq
    · rw [deleteLast_edgeSeg_kept R h2 m hm j hjlt] at hj
      have hjval : ((((j.val : ℕ)) : ZMod R.n)).val = j.val := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      by_cases hj0 : ((j.val : ℕ) : ZMod R.n) = 0
      · have hadj := hS.2.2 ((m : ZMod R.n) + 1)
        rw [hmp1mp1] at hadj
        have hmem : toReal q ∈ R.edgeSeg ((m : ZMod R.n) + 1) ∩ R.edgeSeg 0 :=
          ⟨hqcm, by rw [← hj0]; exact hj⟩
        rw [hadj, Set.mem_singleton_iff] at hmem
        rw [hmem]; exact right_mem_segment ℝ _ _
      · have hne : ((j.val : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) + 1 := by
          intro he
          have hmp1v : (((m : ZMod R.n) + 1)).val = m + 1 := by
            rw [show (m : ZMod R.n) + 1 = (((m + 1 : ℕ)) : ZMod R.n) by push_cast; ring,
              ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          rw [he, hmp1v] at hjval; omega
        have hadj1 : ((j.val : ℕ) : ZMod R.n) + 1 ≠ (m : ZMod R.n) + 1 := by
          intro he; apply hne
          have hjm : ((j.val : ℕ) : ZMod R.n) = (m : ZMod R.n) := by linear_combination he
          rw [hjm] at hjval
          have : ((m : ZMod R.n)).val = m := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          omega
        have hadj2 : ((m : ZMod R.n) + 1) + 1 ≠ ((j.val : ℕ) : ZMod R.n) := by
          rw [hmp1mp1]; exact fun he => hj0 he.symm
        exact (Set.disjoint_left.mp (hS.2.1 _ _ hne hadj1 hadj2) hj hqcm).elim
    · rw [deleteLast_edgeSeg_diag R h2 m hm j hjeq] at hj; exact hj
  · rw [segment_symm]; exact hD

/-- **The `I`/`B` lattice-count additivity (`hIB`), from the three diagonal partition facts.**
Given:
* `hP1` — the interior splits as clip ⊎ ear ⊎ open-diagonal;
* `hP2` — the shared boundary of clip and ear is exactly the closed diagonal;
* `hP3` — the diagonal meets `R`'s boundary exactly at its two endpoints,
this assembles the exact `ValidEarLast` count conjunct, doing all the `ncard` bookkeeping.
The hypotheses are the genuine geometric content; everything below is combinatorics. -/
lemma hIB_of_partition (R : LatticePolygon) (hS : R.IsSimple) (hO : R.PositivelyOriented)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2)
    (hearS : (earTri R m hm).IsSimple)
    (hP1 : R.interiorLattice =
      (deleteLast R h2).interiorLattice ∪ (earTri R m hm).interiorLattice
        ∪ (diagLattice R m \ R.boundaryLattice))
    (hP2 : (deleteLast R h2).boundaryLattice ∩ (earTri R m hm).boundaryLattice
      ⊆ diagLattice R m)
    (hP3 : R.boundaryLattice ∩ diagLattice R m
      ⊆ {R.vert (m : ZMod R.n), R.vert 0}) :
    (R.I : ℝ) + (R.B : ℝ) / 2 = ((deleteLast R h2).I : ℝ) + ((earTri R m hm).I : ℝ)
      + (((deleteLast R h2).B : ℝ) + ((earTri R m hm).B : ℝ)) / 2 - 1 := by
  classical
  -- the reverse inclusions of hP2, hP3 are free (the diagonal is a clip & ear edge;
  -- both endpoints are vertices of `R` and lie on the diagonal), so promote to equalities
  have hP2' : (deleteLast R h2).boundaryLattice ∩ (earTri R m hm).boundaryLattice
      = diagLattice R m := by
    apply Set.Subset.antisymm hP2
    intro q hq
    exact ⟨diagLattice_subset_deleteLast_boundaryLattice R h2 m hm hq,
      diagLattice_subset_earTri_boundaryLattice R m hm hq⟩
  have hP3' : R.boundaryLattice ∩ diagLattice R m
      = {R.vert (m : ZMod R.n), R.vert 0} := by
    apply Set.Subset.antisymm hP3
    intro q hq
    rcases hq with rfl | rfl
    · exact ⟨diag_endpoint_m_mem_R_bdry R m, diag_endpoint_m_mem R m⟩
    · exact ⟨diag_endpoint_0_mem_R_bdry R m, diag_endpoint_0_mem R m⟩
  -- finiteness of all the pieces
  have fCI : (deleteLast R h2).interiorLattice.Finite := interiorLattice_finite _
  have fEI : (earTri R m hm).interiorLattice.Finite := interiorLattice_finite _
  have fCB : (deleteLast R h2).boundaryLattice.Finite := boundaryLattice_finite _
  have fEB : (earTri R m hm).boundaryLattice.Finite := boundaryLattice_finite _
  have fRB : R.boundaryLattice.Finite := boundaryLattice_finite _
  have fD : (diagLattice R m).Finite := diagLattice_finite R h2 m hm
  have fDopen : (diagLattice R m \ R.boundaryLattice).Finite := fD.sdiff
  set d := (diagLattice R m \ R.boundaryLattice).ncard with hd
  -- ========= INTERIOR identity: R.I = clip.I + ear.I + d =========
  -- pairwise disjointness of the three interior pieces
  have hdisjCE : Disjoint (deleteLast R h2).interiorLattice (earTri R m hm).interiorLattice :=
    deleteLast_earTri_interiorLattice_disjoint R hS hO h2 m hm
  -- clip.I ⟂ open-diagonal: open-diagonal ⊆ diagLattice ⊆ clip.boundaryLattice, disjoint from clip.I
  have hdisjCD : Disjoint (deleteLast R h2).interiorLattice
      (diagLattice R m \ R.boundaryLattice) := by
    apply Set.disjoint_of_subset_right (Set.sdiff_subset.trans
      (diagLattice_subset_deleteLast_boundaryLattice R h2 m hm))
    exact interiorLattice_disjoint_boundaryLattice _
  have hdisjED : Disjoint (earTri R m hm).interiorLattice
      (diagLattice R m \ R.boundaryLattice) := by
    apply Set.disjoint_of_subset_right (Set.sdiff_subset.trans
      (diagLattice_subset_earTri_boundaryLattice R m hm))
    exact interiorLattice_disjoint_boundaryLattice _
  have hdisjCE_D : Disjoint
      ((deleteLast R h2).interiorLattice ∪ (earTri R m hm).interiorLattice)
      (diagLattice R m \ R.boundaryLattice) := Set.disjoint_union_left.2 ⟨hdisjCD, hdisjED⟩
  -- count R.I via hP1 (two disjoint unions)
  have hRI : R.I = (deleteLast R h2).I + (earTri R m hm).I + d := by
    have h1 : R.interiorLattice.ncard =
        ((deleteLast R h2).interiorLattice ∪ (earTri R m hm).interiorLattice).ncard
          + (diagLattice R m \ R.boundaryLattice).ncard := by
      rw [hP1, Set.ncard_union_eq hdisjCE_D (fCI.union fEI) fDopen]
    have h2' : ((deleteLast R h2).interiorLattice ∪ (earTri R m hm).interiorLattice).ncard
        = (deleteLast R h2).interiorLattice.ncard + (earTri R m hm).interiorLattice.ncard :=
      Set.ncard_union_eq hdisjCE fCI fEI
    show R.interiorLattice.ncard = _
    rw [h1, h2', hd]
    rfl
  -- ========= BOUNDARY identity: clip.B + ear.B = R.B + 2d + 2 =========
  -- |Dset| = d + 2
  have hDcard : (diagLattice R m).ncard = d + 2 := by
    -- Dset = (Dset \ RB) ⊎ (Dset ∩ RB), the two pieces disjoint
    have hpart : (diagLattice R m \ R.boundaryLattice) ∪ (diagLattice R m ∩ R.boundaryLattice)
        = diagLattice R m := Set.sdiff_union_inter _ _
    have hdisj : Disjoint (diagLattice R m \ R.boundaryLattice)
        (diagLattice R m ∩ R.boundaryLattice) := Set.disjoint_sdiff_inter
    have hsplit : (diagLattice R m).ncard
        = (diagLattice R m \ R.boundaryLattice).ncard
          + (diagLattice R m ∩ R.boundaryLattice).ncard := by
      conv_lhs => rw [← hpart]
      rw [Set.ncard_union_eq hdisj fDopen (fD.inter_of_left _)]
    have hinter : (diagLattice R m ∩ R.boundaryLattice).ncard = 2 := by
      rw [Set.inter_comm, hP3', diag_endpoints_ncard R m hm hearS]
    rw [hsplit, hinter, hd]
  -- bridge the `.B` projections to `.boundaryLattice.ncard` (definitional) for omega
  have hBdefR : R.B = R.boundaryLattice.ncard := rfl
  have hBdefC : (deleteLast R h2).B = (deleteLast R h2).boundaryLattice.ncard := rfl
  have hBdefE : (earTri R m hm).B = (earTri R m hm).boundaryLattice.ncard := rfl
  -- R.B ∩ Dset = {vm, v0}, so |R.B ∩ Dset| = 2
  have hRBD : (R.boundaryLattice ∩ diagLattice R m).ncard = 2 := by
    rw [hP3', diag_endpoints_ncard R m hm hearS]
  -- |R.B ∪ Dset| = R.B + d   (inclusion-exclusion with |R.B ∩ Dset| = 2 and |Dset| = d+2)
  have hRunionD : (R.boundaryLattice ∪ diagLattice R m).ncard = R.boundaryLattice.ncard + d := by
    have hie := Set.ncard_union_add_ncard_inter R.boundaryLattice (diagLattice R m) fRB fD
    rw [hRBD, hDcard] at hie
    omega
  -- clip.B ∪ ear.B = R.B ∪ Dset, and clip.B ∩ ear.B = Dset
  have hUnion := boundaryLattice_deleteLast_union_earTri R h2 m hm
  have hBsum : (deleteLast R h2).B + (earTri R m hm).B = R.B + 2 * d + 2 := by
    have hie := Set.ncard_union_add_ncard_inter
      (deleteLast R h2).boundaryLattice (earTri R m hm).boundaryLattice fCB fEB
    rw [hP2', hUnion, hRunionD, hDcard] at hie
    rw [hBdefR, hBdefC, hBdefE]
    omega
  -- ========= COMBINE over ℝ =========
  have hRI' : (R.I : ℝ) = (deleteLast R h2).I + (earTri R m hm).I + d := by
    rw [hRI]; push_cast; ring
  have hBsum' : ((deleteLast R h2).B : ℝ) + (earTri R m hm).B = R.B + 2 * d + 2 := by
    exact_mod_cast hBsum
  rw [hRI', hBsum']; ring

/-! ### Real-point triangle interior winding (the ear-inside foundation)

The lattice-point triangle winding characterisation (`winding_eq_one_of_crossZ_pos`)
is stated for `q : Pt`. The ear-inside fact needs it for *real* points filling the
open ear triangle. We re-derive the crossing-count facts over `ℝ × ℝ` (they only use
the real heights `(toReal vⱼ).2` and the real `cross`, so the integer machinery
generalises verbatim). -/

/-- **Real-coordinate winding sum (all edges CCW).** If `q : ℝ × ℝ` sees every edge
counter-clockwise (`0 < cross (vⱼ − q) (vⱼ₊₁ − q)`), the winding is the number of
upward crossings. Real analogue of `winding_of_crossZ_pos`. -/
lemma winding_of_cross_pos_real (P : LatticePolygon) (q : ℝ × ℝ)
    (h : ∀ j, 0 < cross (toReal (P.vert j) - q) (toReal (P.vert (j + 1)) - q)) :
    P.winding q
      = ∑ j, (if (toReal (P.vert j)).2 ≤ q.2 ∧ q.2 < (toReal (P.vert (j + 1))).2
          then (1 : ℤ) else 0) := by
  rw [LatticePolygon.winding]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpos : 0 < cross (toReal (P.vert (j + 1)) - toReal (P.vert j))
      (q - toReal (P.vert j)) := by
    have := h j
    rwa [show cross (toReal (P.vert (j + 1)) - toReal (P.vert j)) (q - toReal (P.vert j))
        = cross (toReal (P.vert j) - q) (toReal (P.vert (j + 1)) - q) from by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring]
  unfold LatticePolygon.edgeWind
  have hc : ¬ cross (toReal (P.vert (j + 1)) - toReal (P.vert j)) (q - toReal (P.vert j)) < 0 :=
    not_lt.mpr hpos.le
  simp only [hpos, hc, and_true, and_false, if_false]

/-- Indicator identity (subtraction form): the directed crossing difference equals the
`≤`-indicator difference. Abstract over three reals to keep the context clean. -/
private lemma crossing_sub_indicator (a b c : ℝ) :
    (if a ≤ c ∧ c < b then (1 : ℤ) else 0) - (if b ≤ c ∧ c < a then (1 : ℤ) else 0)
      = (if a ≤ c then (1 : ℤ) else 0) - (if b ≤ c then (1 : ℤ) else 0) := by
  split_ifs <;> simp_all <;> linarith

/-- Indicator identity (sum/abs form): the total directed crossing count equals the
absolute `≤`-indicator difference. -/
private lemma crossing_add_indicator (a b c : ℝ) :
    (if a ≤ c ∧ c < b then (1 : ℤ) else 0) + (if b ≤ c ∧ c < a then (1 : ℤ) else 0)
      = |(if a ≤ c then (1 : ℤ) else 0) - (if b ≤ c then (1 : ℤ) else 0)| := by
  split_ifs <;> simp_all <;> linarith

/-- **Real-coordinate crossing balance.** Upward and downward crossings of the
horizontal line `y = q.2` agree. Real analogue of `sum_upward_eq_downward`. -/
lemma sum_upward_eq_downward_real (P : LatticePolygon) (q : ℝ × ℝ) :
    (∑ j, (if (toReal (P.vert j)).2 ≤ q.2 ∧ q.2 < (toReal (P.vert (j + 1))).2
        then (1 : ℤ) else 0))
      = ∑ j, (if (toReal (P.vert (j + 1))).2 ≤ q.2 ∧ q.2 < (toReal (P.vert j)).2
          then (1 : ℤ) else 0) := by
  have key : ∀ j : ZMod P.n,
      (if (toReal (P.vert j)).2 ≤ q.2 ∧ q.2 < (toReal (P.vert (j + 1))).2 then (1 : ℤ) else 0)
        - (if (toReal (P.vert (j + 1))).2 ≤ q.2 ∧ q.2 < (toReal (P.vert j)).2 then (1 : ℤ) else 0)
      = (if (toReal (P.vert j)).2 ≤ q.2 then (1 : ℤ) else 0)
        - (if (toReal (P.vert (j + 1))).2 ≤ q.2 then (1 : ℤ) else 0) := fun j =>
    crossing_sub_indicator (toReal (P.vert j)).2 (toReal (P.vert (j + 1))).2 q.2
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun j _ => key j),
    Finset.sum_sub_distrib, sub_eq_zero]
  exact (Fintype.sum_equiv (Equiv.addRight 1)
    (fun j => if (toReal (P.vert (j + 1))).2 ≤ q.2 then (1 : ℤ) else 0)
    (fun j => if (toReal (P.vert j)).2 ≤ q.2 then (1 : ℤ) else 0) (fun _ => rfl)).symm

/-- **Real-coordinate total crossings = 2** for a straddled triangle. Real analogue of
`sum_crossing_eq_two`. -/
lemma sum_crossing_eq_two_real (P : LatticePolygon) (hn : P.n = 3) (q : ℝ × ℝ)
    (hlo : ∃ j, (toReal (P.vert j)).2 ≤ q.2) (hhi : ∃ j, q.2 < (toReal (P.vert j)).2) :
    (∑ j, ((if (toReal (P.vert j)).2 ≤ q.2 ∧ q.2 < (toReal (P.vert (j + 1))).2 then (1 : ℤ) else 0)
      + (if (toReal (P.vert (j + 1))).2 ≤ q.2 ∧ q.2 < (toReal (P.vert j)).2
          then (1 : ℤ) else 0))) = 2 := by
  have hterm : ∀ j : ZMod P.n,
      (if (toReal (P.vert j)).2 ≤ q.2 ∧ q.2 < (toReal (P.vert (j + 1))).2 then (1 : ℤ) else 0)
        + (if (toReal (P.vert (j + 1))).2 ≤ q.2 ∧ q.2 < (toReal (P.vert j)).2 then (1 : ℤ) else 0)
      = |(if (toReal (P.vert j)).2 ≤ q.2 then (1 : ℤ) else 0)
          - (if (toReal (P.vert (j + 1))).2 ≤ q.2 then (1 : ℤ) else 0)| := fun j =>
    crossing_add_indicator (toReal (P.vert j)).2 (toReal (P.vert (j + 1))).2 q.2
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  obtain ⟨e1, e2, e3, _, _, _⟩ := zmodPn_idx P hn
  obtain ⟨jlo, hjlo⟩ := hlo
  obtain ⟨jhi, hjhi⟩ := hhi
  have ho : (if (toReal (P.vert 0)).2 ≤ q.2 then (1 : ℤ) else 0) = 1
      ∨ (if (toReal (P.vert 1)).2 ≤ q.2 then (1 : ℤ) else 0) = 1
      ∨ (if (toReal (P.vert 2)).2 ≤ q.2 then (1 : ℤ) else 0) = 1 := by
    rcases zmodPn_cases P hn jlo with h | h | h <;> subst h
    · exact Or.inl (if_pos hjlo)
    · exact Or.inr (Or.inl (if_pos hjlo))
    · exact Or.inr (Or.inr (if_pos hjlo))
  have hz : (if (toReal (P.vert 0)).2 ≤ q.2 then (1 : ℤ) else 0) = 0
      ∨ (if (toReal (P.vert 1)).2 ≤ q.2 then (1 : ℤ) else 0) = 0
      ∨ (if (toReal (P.vert 2)).2 ≤ q.2 then (1 : ℤ) else 0) = 0 := by
    rcases zmodPn_cases P hn jhi with h | h | h <;> subst h
    · exact Or.inl (if_neg (not_le.mpr hjhi))
    · exact Or.inr (Or.inl (if_neg (not_le.mpr hjhi)))
    · exact Or.inr (Or.inr (if_neg (not_le.mpr hjhi)))
  rw [sum_zmodPn P hn (fun j => |(if (toReal (P.vert j)).2 ≤ q.2 then (1 : ℤ) else 0)
      - (if (toReal (P.vert (j + 1))).2 ≤ q.2 then (1 : ℤ) else 0)|), e1, e2, e3]
  exact indicator_diff_abs_sum _ _ _ (by split_ifs <;> simp) (by split_ifs <;> simp)
    (by split_ifs <;> simp) hz ho

/-- **Real-point triangle interior winding = 1.** For a triangle (`P.n = 3`), any real
point `q` that sees every edge strictly CCW (`0 < cross (vⱼ − q) (vⱼ₊₁ − q)` for all `j`)
and whose height is straddled by the vertices has `P.winding q = 1`. Real analogue of
`winding_eq_one_of_crossZ_pos`. -/
lemma winding_eq_one_of_cross_pos_real (P : LatticePolygon) (hn : P.n = 3) (q : ℝ × ℝ)
    (h : ∀ j, 0 < cross (toReal (P.vert j) - q) (toReal (P.vert (j + 1)) - q))
    (hlo : ∃ j, (toReal (P.vert j)).2 ≤ q.2) (hhi : ∃ j, q.2 < (toReal (P.vert j)).2) :
    P.winding q = 1 := by
  rw [winding_of_cross_pos_real P q h]
  have htot := sum_crossing_eq_two_real P hn q hlo hhi
  have hbal := sum_upward_eq_downward_real P q
  rw [Finset.sum_add_distrib, ← hbal] at htot
  omega

/-- **Real barycentric-`y` identity.** For real points, the `y`-coordinate of `q`
scaled by the sum of the three corner cross products equals the cross-weighted sum of
vertex heights. Pure `ring`; the real analogue of `barycentric_y`. -/
lemma barycentric_y_real (q v0 v1 v2 : ℝ × ℝ) :
    q.2 * (cross (v0 - q) (v1 - q) + cross (v1 - q) (v2 - q) + cross (v2 - q) (v0 - q))
      = cross (v1 - q) (v2 - q) * v0.2 + cross (v2 - q) (v0 - q) * v1.2
        + cross (v0 - q) (v1 - q) * v2.2 := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- **A vertex lies strictly below an interior point.** If `q` sees all three edges of
a triangle strictly CCW, some vertex is strictly below `q`. Real analogue of
`exists_vertex_below`. -/
lemma exists_vertex_below_real (q v0 v1 v2 : ℝ × ℝ)
    (h0 : 0 < cross (v0 - q) (v1 - q)) (h1 : 0 < cross (v1 - q) (v2 - q))
    (h2 : 0 < cross (v2 - q) (v0 - q)) :
    v0.2 < q.2 ∨ v1.2 < q.2 ∨ v2.2 < q.2 := by
  by_contra h
  push Not at h
  obtain ⟨hv0, hv1, hv2⟩ := h
  have key : cross (v1 - q) (v2 - q) * (v0.2 - q.2) + cross (v2 - q) (v0 - q) * (v1.2 - q.2)
      + cross (v0 - q) (v1 - q) * (v2.2 - q.2) = 0 := by
    linear_combination -barycentric_y_real q v0 v1 v2
  have t0 := mul_nonneg h1.le (sub_nonneg.2 hv0)
  have t1 := mul_nonneg h2.le (sub_nonneg.2 hv1)
  have t2 := mul_nonneg h0.le (sub_nonneg.2 hv2)
  have z0 : cross (v1 - q) (v2 - q) * (v0.2 - q.2) = 0 := by linarith
  have z1 : cross (v2 - q) (v0 - q) * (v1.2 - q.2) = 0 := by linarith
  have e0 : v0.2 - q.2 = 0 := (mul_eq_zero.1 z0).resolve_left (by linarith)
  have e1 : v1.2 - q.2 = 0 := (mul_eq_zero.1 z1).resolve_left (by linarith)
  have hc0 : cross (v0 - q) (v1 - q) = 0 := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]
    rw [show v0.2 - q.2 = 0 by linarith, show v1.2 - q.2 = 0 by linarith]; ring
  linarith

/-- **A vertex lies strictly above an interior point.** Real analogue of
`exists_vertex_above`. -/
lemma exists_vertex_above_real (q v0 v1 v2 : ℝ × ℝ)
    (h0 : 0 < cross (v0 - q) (v1 - q)) (h1 : 0 < cross (v1 - q) (v2 - q))
    (h2 : 0 < cross (v2 - q) (v0 - q)) :
    q.2 < v0.2 ∨ q.2 < v1.2 ∨ q.2 < v2.2 := by
  by_contra h
  push Not at h
  obtain ⟨hv0, hv1, hv2⟩ := h
  have key : cross (v1 - q) (v2 - q) * (q.2 - v0.2) + cross (v2 - q) (v0 - q) * (q.2 - v1.2)
      + cross (v0 - q) (v1 - q) * (q.2 - v2.2) = 0 := by
    linear_combination barycentric_y_real q v0 v1 v2
  have t0 := mul_nonneg h1.le (sub_nonneg.2 hv0)
  have t1 := mul_nonneg h2.le (sub_nonneg.2 hv1)
  have t2 := mul_nonneg h0.le (sub_nonneg.2 hv2)
  have z0 : cross (v1 - q) (v2 - q) * (q.2 - v0.2) = 0 := by linarith
  have z1 : cross (v2 - q) (v0 - q) * (q.2 - v1.2) = 0 := by linarith
  have e0 : q.2 - v0.2 = 0 := (mul_eq_zero.1 z0).resolve_left (by linarith)
  have e1 : q.2 - v1.2 = 0 := (mul_eq_zero.1 z1).resolve_left (by linarith)
  have hc0 : cross (v0 - q) (v1 - q) = 0 := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]
    rw [show v0.2 - q.2 = 0 by linarith, show v1.2 - q.2 = 0 by linarith]; ring
  linarith

/-- **Real-point triangle interior winding = 1, straddle-free.** For a triangle, any
real point seeing all three edges strictly CCW (`0 < cross (vⱼ − q) (vⱼ₊₁ − q)`) has
`P.winding q = 1`. The vertical-straddle hypotheses are now automatic
(`exists_vertex_below_real` / `exists_vertex_above_real`). Real analogue of
`winding_eq_one_of_crossZ_pos'`. -/
lemma winding_eq_one_of_three_cross_pos_real (P : LatticePolygon) (hn : P.n = 3) (q : ℝ × ℝ)
    (h : ∀ j, 0 < cross (toReal (P.vert j) - q) (toReal (P.vert (j + 1)) - q)) :
    P.winding q = 1 := by
  obtain ⟨e1, e2, e3, _, _, _⟩ := zmodPn_idx P hn
  have h0 := h 0; rw [e1] at h0
  have h1 := h 1; rw [e2] at h1
  have h2 := h 2; rw [e3] at h2
  refine winding_eq_one_of_cross_pos_real P hn q h ?_ ?_
  · rcases exists_vertex_below_real q (toReal (P.vert 0)) (toReal (P.vert 1)) (toReal (P.vert 2))
        h0 h1 h2 with hb | hb | hb
    · exact ⟨0, hb.le⟩
    · exact ⟨1, hb.le⟩
    · exact ⟨2, hb.le⟩
  · rcases exists_vertex_above_real q (toReal (P.vert 0)) (toReal (P.vert 1)) (toReal (P.vert 2))
        h0 h1 h2 with ha | ha | ha
    · exact ⟨0, ha⟩
    · exact ⟨1, ha⟩
    · exact ⟨2, ha⟩

/-! ### Convex vertex existence (Meisters, unique-lowest case)

When the lex-lowest vertex is the unique minimum-height vertex, both its neighbours are
strictly above it, so `cornerCross_pos_lex_lowest_winding` applies and the corner is a
strict left turn. This is the clean (non-flat-bottom) half of the convex-vertex step. -/

/-- **Strict neighbours from a unique lowest vertex.** If the lex-lowest vertex `m` is
the unique minimum-height vertex (`huniq`), then both neighbours `vₘ₋₁, vₘ₊₁` are
strictly above it. (They differ from `m`, hence have a different height, hence — being
weakly above by `lex_lowest_all_above` — strictly above.) -/
lemma lex_lowest_strict_neighbours_of_unique (P : LatticePolygon) (h2 : 2 ≤ P.n)
    (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (huniq : ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert m)).2 → j = m) :
    (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2 ∧
    (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2 := by
  haveI : NeZero P.n := ⟨by omega⟩
  have hone : (1 : ZMod P.n) ≠ 0 := by
    intro hc
    have : (1 : ZMod P.n).val = (0 : ZMod P.n).val := by rw [hc]
    rw [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)] at this
    exact one_ne_zero this
  have hnext : m + 1 ≠ m := by
    intro hc
    apply hone
    have : m + 1 = m + 0 := by rw [hc, add_zero]
    exact add_left_cancel this
  have hprev : m - 1 ≠ m := by
    intro hc
    apply hnext
    have : (m - 1) + 1 = m + 1 := by rw [hc]
    rw [sub_add_cancel] at this
    exact this.symm
  have hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2 := by
    have hge := lex_lowest_all_above P m hlex (m - 1)
    rcases eq_or_lt_of_le hge with heq | hlt
    · exact absurd (huniq (m - 1) heq.symm) hprev
    · exact hlt
  have hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2 := by
    have hge := lex_lowest_all_above P m hlex (m + 1)
    rcases eq_or_lt_of_le hge with heq | hlt
    · exact absurd (huniq (m + 1) heq.symm) hnext
    · exact hlt
  exact ⟨hba, hbc⟩

/-- **The unique lowest vertex is convex.** For a simple positively-oriented polygon
whose lex-lowest vertex `m` is the unique minimum-height vertex, the corner at `m` is a
strict left turn: `0 < cornerCross P m`. Strict neighbours come from uniqueness; the
sign from `cornerCross_pos_lex_lowest_winding`. -/
lemma cornerCross_pos_unique_lowest (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) (h2 : 2 ≤ P.n) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (huniq : ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert m)).2 → j = m) :
    0 < cornerCross P m := by
  obtain ⟨hba, hbc⟩ := lex_lowest_strict_neighbours_of_unique P h2 m hlex huniq
  exact cornerCross_pos_lex_lowest_winding P hS hO m hlex huniq hba hbc

/-- **Convex vertex existence (Meisters).** Every simple, positively-oriented lattice
polygon has a convex vertex: `∃ i, 0 < cornerCross P i`. This handles the flat-bottom
degeneracy via a generic lattice **shear** `S(x,y) = (x, y + k·x)`: choosing `k` so all
sheared heights are distinct (`exists_generic_shear`) makes the lex-lowest vertex of
`shearP P k` the *unique* minimum-height vertex, so `cornerCross_pos_unique_lowest`
applies; the shear preserves `cornerCross` (`shearP_cornerCross`), transporting the
strict left turn back to `P`. -/
theorem exists_convex_vertex (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) : ∃ i : ZMod P.n, 0 < cornerCross P i := by
  -- pick a separating shear coefficient
  obtain ⟨k, hk⟩ := exists_generic_shear P hS
  set Q := shearP P k with hQ
  have hQS : Q.IsSimple := shearP_isSimple P k hS
  have hQO : Q.PositivelyOriented := shearP_positivelyOriented P k hO
  have h2 : 2 ≤ Q.n := by
    have := simple_imp_three_le_n Q hQS; omega
  -- the lex-lowest vertex of `Q`
  obtain ⟨m, hlex⟩ := exists_lex_lowest_vertex Q
  -- it is the *unique* minimum-height vertex, since all sheared heights are distinct
  have huniq : ∀ j : ZMod Q.n,
      (toReal (Q.vert j)).2 = (toReal (Q.vert m)).2 → j = m := by
    intro j hjeq
    by_contra hjm
    -- sheared real heights coincide ⟹ the integer sheared heights coincide
    have hzeq : (Q.vert j).2 = (Q.vert m).2 := by
      have := hjeq; simp only [toReal] at this; exact_mod_cast this
    have hint : (P.vert j).2 + k * (P.vert j).1 = (P.vert m).2 + k * (P.vert m).1 := by
      -- `Q.vert _` is defeq to the sheared coordinate via the `let`-binding `Q := shearP P k`
      exact hzeq
    exact hk j m hjm hint
  -- convex at the unique lowest vertex, transported back through the shear
  have hpos : 0 < cornerCross Q m := cornerCross_pos_unique_lowest Q hQS hQO h2 m hlex huniq
  exact ⟨m, by rw [← shearP_cornerCross P k m]; exact hpos⟩

/-- **Direction-extreme vertex is convex.** If the integer functional `(x,y) ↦ c·x + d·y`
(`(c,d) ≠ 0`) is injective on the vertices, the vertex `m` minimising it is convex
(`0 < cornerCross P m`).  Proof: apply the linear map `linP P c d` (determinant `c² + d²`),
whose *height* is exactly this functional; injectivity makes `m` the unique lowest vertex of
`linP P c d`, so `cornerCross_pos_unique_lowest` gives `0 < cornerCross (linP P c d) m`, and
`linP_cornerCross` (sign-preserving since `c² + d² > 0`) transports this back to `P`. -/
lemma exists_convex_min (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (h2 : 2 ≤ P.n) (c d : ℤ) (hcd : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 ≠ 0)
    (hinj : ∀ i j : ZMod P.n, (c : ℝ) * (P.vert i).1 + (d : ℝ) * (P.vert i).2
        = (c : ℝ) * (P.vert j).1 + (d : ℝ) * (P.vert j).2 → i = j) :
    ∃ m : ZMod P.n, 0 < cornerCross P m ∧
      ∀ j : ZMod P.n, (c : ℝ) * (P.vert m).1 + (d : ℝ) * (P.vert m).2
        ≤ (c : ℝ) * (P.vert j).1 + (d : ℝ) * (P.vert j).2 := by
  have hpos : (0 : ℝ) < (c : ℝ) ^ 2 + (d : ℝ) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hcd)
  set Q := linP P c d with hQ
  have hQS : Q.IsSimple := linP_isSimple P c d hcd hS
  have hQO : Q.PositivelyOriented := linP_positivelyOriented P c d hpos hO
  have hQ2 : 2 ≤ Q.n := by show 2 ≤ P.n; exact h2
  have hht : ∀ i : ZMod Q.n,
      (toReal (Q.vert i)).2 = (c : ℝ) * (P.vert i).1 + (d : ℝ) * (P.vert i).2 :=
    fun i => linP_height P c d i
  obtain ⟨m, hlex⟩ := exists_lex_lowest_vertex Q
  have huniq : ∀ j : ZMod Q.n, (toReal (Q.vert j)).2 = (toReal (Q.vert m)).2 → j = m := by
    intro j hj
    rw [hht, hht] at hj
    exact hinj j m hj
  have hposQ : 0 < cornerCross Q m := cornerCross_pos_unique_lowest Q hQS hQO hQ2 m hlex huniq
  have htrans : cornerCross Q m = ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) * cornerCross P m :=
    linP_cornerCross P c d m
  rw [htrans] at hposQ
  refine ⟨m, ?_, ?_⟩
  · nlinarith [hposQ, hpos]
  · intro j
    have hZ : (Q.vert m).2 ≤ (Q.vert j).2 := by
      rcases Prod.Lex.le_iff.mp (hlex j) with hlt | ⟨heq, _⟩
      · exact le_of_lt hlt
      · exact le_of_eq heq
    have hR : ((Q.vert m).2 : ℝ) ≤ ((Q.vert j).2 : ℝ) := by exact_mod_cast hZ
    have em : ((Q.vert m).2 : ℝ) = (toReal (Q.vert m)).2 := rfl
    have ej : ((Q.vert j).2 : ℝ) = (toReal (Q.vert j)).2 := rfl
    rw [em, ej, hht, hht] at hR
    exact hR

/-- The perturbed functional's coefficient vector `(d1 − sN·d2, d2 + sN·d1)` is nonzero
whenever `(d1, d2)` is. Factored out of `exists_offline_convex`. -/
private lemma perturb_sq_ne_zero (d1 d2 s N : ℤ) (hd0 : ¬(d1 = 0 ∧ d2 = 0)) :
    ((d1 - s * N * d2 : ℤ) : ℝ) ^ 2 + ((d2 + s * N * d1 : ℤ) : ℝ) ^ 2 ≠ 0 := by
  intro h
  have h1 : ((d1 - s * N * d2 : ℤ) : ℝ) ^ 2 = 0 ∧ ((d2 + s * N * d1 : ℤ) : ℝ) ^ 2 = 0 :=
    (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h
  have e1 : d1 - s * N * d2 = 0 := by
    have := pow_eq_zero_iff two_ne_zero |>.mp h1.1
    exact_mod_cast this
  have e2 : d2 + s * N * d1 = 0 := by
    have := pow_eq_zero_iff two_ne_zero |>.mp h1.2
    exact_mod_cast this
  have key1 : d1 * (1 + (s * N) ^ 2) = 0 := by linear_combination e1 + (s * N) * e2
  have hd1z : d1 = 0 := by
    have hposN : (0 : ℤ) < 1 + (s * N) ^ 2 := by positivity
    rcases mul_eq_zero.1 key1 with h' | h'
    · exact h'
    · omega
  have hd2z : d2 = 0 := by rw [hd1z, mul_zero, add_zero] at e2; exact e2
  exact hd0 ⟨hd1z, hd2z⟩

/-- **Injectivity of the perturbed integer functional** `FL = sN·PL + QL` on the vertices:
on a `PL`-level set it pins the vertex down via `d1² + d2² ≠ 0`, and across `PL`-levels the
`sN` multiple dominates the `QL`-spread. Factored out of `exists_offline_convex`. -/
private lemma perturb_functional_inj (P : LatticePolygon) (hS : P.IsSimple)
    (d1 d2 s N : ℤ) (PL QL FL : ZMod P.n → ℤ)
    (hPL : ∀ i, PL i = -d2 * (P.vert i).1 + d1 * (P.vert i).2)
    (hQL : ∀ i, QL i = d1 * (P.vert i).1 + d2 * (P.vert i).2)
    (hFL : ∀ i, FL i = s * N * PL i + QL i)
    (hsqpos : 0 < d1 ^ 2 + d2 ^ 2) (hs1 : s = 1 ∨ s = -1)
    (hNpos : 0 < N) (hNgt : ∀ i j : ZMod P.n, |QL i - QL j| < N) :
    ∀ i j : ZMod P.n, FL i = FL j → i = j := by
  intro i j hF
  rw [hFL i, hFL j] at hF
  by_cases hpl : PL i = PL j
  · have hql : QL i = QL j := by rw [hpl] at hF; linarith
    have hPLd : PL i - PL j = 0 := by rw [hpl]; ring
    have hQLd : QL i - QL j = 0 := by rw [hql]; ring
    have kx : (d1 ^ 2 + d2 ^ 2) * ((P.vert i).1 - (P.vert j).1)
        = d1 * (QL i - QL j) - d2 * (PL i - PL j) := by
      rw [hPL i, hPL j, hQL i, hQL j]; ring
    have ky : (d1 ^ 2 + d2 ^ 2) * ((P.vert i).2 - (P.vert j).2)
        = d1 * (PL i - PL j) + d2 * (QL i - QL j) := by
      rw [hPL i, hPL j, hQL i, hQL j]; ring
    rw [hQLd, hPLd] at kx ky
    simp only [mul_zero, sub_zero, add_zero] at kx ky
    have hxx : (P.vert i).1 = (P.vert j).1 := by
      rcases mul_eq_zero.1 kx with h' | h'
      · exact absurd h' (ne_of_gt hsqpos)
      · exact sub_eq_zero.1 h'
    have hyy : (P.vert i).2 = (P.vert j).2 := by
      rcases mul_eq_zero.1 ky with h' | h'
      · exact absurd h' (ne_of_gt hsqpos)
      · exact sub_eq_zero.1 h'
    exact vert_injective P hS (Prod.ext hxx hyy)
  · exfalso
    have hdiff : s * N * PL i - s * N * PL j = QL j - QL i := by linarith
    have heq : s * N * (PL i - PL j) = QL j - QL i := by rw [← hdiff]; ring
    have hpld1 : (1 : ℤ) ≤ |PL i - PL j| := Int.one_le_abs (sub_ne_zero.2 hpl)
    have hsabs : |s| = 1 := by rcases hs1 with h' | h' <;> rw [h'] <;> decide
    have habs : |s * N * (PL i - PL j)| = |QL j - QL i| := by rw [heq]
    have hge : N ≤ |s * N * (PL i - PL j)| := by
      rw [abs_mul, abs_mul, hsabs, abs_of_pos hNpos, one_mul]
      have h := mul_le_mul_of_nonneg_left hpld1 (le_of_lt hNpos)
      rw [mul_one] at h; exact h
    rw [habs] at hge
    linarith [hNgt j i, hge]

/-- **The functional's minimiser is off the line.** If `FL w ≤ FL t` yet `PL w = PL a`,
the `sN` multiple of the `PL`-drop toward `t` overwhelms the `QL`-spread — contradiction.
Factored out of `exists_offline_convex`. -/
private lemma perturb_min_off_line (s N PLw PLa PLt QLw QLt : ℤ)
    (hs : s * (PLt - PLa) < 0) (hNpos : 0 < N) (hNgt : |QLt - QLw| < N)
    (hmin : s * N * PLw + QLw ≤ s * N * PLt + QLt) (hwa : PLw = PLa) : False := by
  rw [hwa] at hmin
  have hle2 : s * N * PLa - s * N * PLt ≤ QLt - QLw := by linarith
  have hM : N ≤ s * N * PLa - s * N * PLt := by
    have he : s * N * PLa - s * N * PLt = N * (-(s * (PLt - PLa))) := by ring
    rw [he]
    have h1 : 1 ≤ -(s * (PLt - PLa)) := by omega
    have h := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rw [mul_one] at h; exact h
  have hlt : QLt - QLw < N := lt_of_le_of_lt (le_abs_self _) hNgt
  linarith

/-- **Some vertex is strictly off the chord `v_a v_b`.** The positive fan term at `a`
(`exists_pos_fan_term`) forbids all vertices from being collinear with the chord. -/
private lemma exists_cross_ne (P : LatticePolygon) (hO : P.PositivelyOriented)
    (a b : ZMod P.n) (hne : P.vert a ≠ P.vert b) :
    ∃ t : ZMod P.n, cross (toReal (P.vert b) - toReal (P.vert a))
      (toReal (P.vert t) - toReal (P.vert a)) ≠ 0 := by
  have hDne : toReal (P.vert b) - toReal (P.vert a) ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hne ((toReal_injective h).symm)
  have hpar : ∀ u w : ℝ × ℝ,
      cross (toReal (P.vert b) - toReal (P.vert a)) u = 0 →
      cross (toReal (P.vert b) - toReal (P.vert a)) w = 0 → cross u w = 0 := by
    intro u w hu hw
    set D := toReal (P.vert b) - toReal (P.vert a) with hDdef
    have h1 : D.1 * cross u w = 0 := by
      simp only [cross] at hu hw ⊢; linear_combination u.1 * hw - w.1 * hu
    have h2 : D.2 * cross u w = 0 := by
      simp only [cross] at hu hw ⊢; linear_combination u.2 * hw - w.2 * hu
    by_cases hD1z : D.1 = 0
    · have hD2z : D.2 ≠ 0 := fun h => hDne (Prod.ext hD1z h)
      exact (mul_eq_zero.1 h2).resolve_left hD2z
    · exact (mul_eq_zero.1 h1).resolve_left hD1z
  obtain ⟨i0, hi0⟩ := exists_pos_fan_term P hO a
  by_contra hcon
  push Not at hcon
  exact absurd (hpar _ _ (hcon i0) (hcon (i0 + 1))) (ne_of_gt hi0)

/-- **The perturbed integer functional.** Given the chord's level functionals `PL`, `QL`
and a vertex `t` with `PL t ≠ PL a`, produce coefficients `c, dc` whose vertex functional
`FL` is injective, decomposes as `sN·PL + QL` with `N` dominating the `QL`-spread, and
strictly decreases from `a` toward `t`. -/
private lemma exists_perturbed_functional (P : LatticePolygon) (hS : P.IsSimple)
    (d1 d2 : ℤ) (hd0 : ¬(d1 = 0 ∧ d2 = 0)) (PL QL : ZMod P.n → ℤ)
    (hPL : ∀ i, PL i = -d2 * (P.vert i).1 + d1 * (P.vert i).2)
    (hQL : ∀ i, QL i = d1 * (P.vert i).1 + d2 * (P.vert i).2)
    (t a : ZMod P.n) (ht : PL t ≠ PL a) :
    ∃ (c dc s N : ℤ) (FL : ZMod P.n → ℤ),
      (∀ i, c * (P.vert i).1 + dc * (P.vert i).2 = FL i) ∧
      ((c : ℝ) ^ 2 + (dc : ℝ) ^ 2 ≠ 0) ∧
      (∀ i j : ZMod P.n, FL i = FL j → i = j) ∧
      (∀ i, FL i = s * N * PL i + QL i) ∧
      0 < N ∧ (∀ i j : ZMod P.n, |QL i - QL j| < N) ∧
      s * (PL t - PL a) < 0 := by
  classical
  have hsqpos : 0 < d1 ^ 2 + d2 ^ 2 := by
    have hne0 : d1 ^ 2 + d2 ^ 2 ≠ 0 := by
      intro h; apply hd0; constructor <;> nlinarith [sq_nonneg d1, sq_nonneg d2]
    exact lt_of_le_of_ne (by positivity) (Ne.symm hne0)
  -- the sign `s` and the spread bound `N`, kept fully opaque: the defining terms (an
  -- `if` and a `Finset.sum` over `ZMod P.n × ZMod P.n`) must not leak into the context,
  -- or every later tactic pays for attempts to evaluate them (~50× heartbeat blowup).
  obtain ⟨s, hs1, hs⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ s * (PL t - PL a) < 0 := by
    rcases lt_or_gt_of_ne ht with h | h
    · exact ⟨1, Or.inl rfl, by omega⟩
    · exact ⟨-1, Or.inr rfl, by omega⟩
  obtain ⟨N, hNpos, hNgt⟩ : ∃ N : ℤ, 0 < N ∧ ∀ i j : ZMod P.n, |QL i - QL j| < N := by
    obtain ⟨B, hB⟩ :=
      (Set.finite_range fun p : ZMod P.n × ZMod P.n => |QL p.1 - QL p.2|).bddAbove
    refine ⟨max B 0 + 1, by have := le_max_right B 0; omega, fun i j => ?_⟩
    have h1 : |QL i - QL j| ≤ B := hB ⟨(i, j), rfl⟩
    have h2 : B ≤ max B 0 := le_max_left _ _
    omega
  have hFLeq : ∀ i, (d1 - s * N * d2) * (P.vert i).1 + (d2 + s * N * d1) * (P.vert i).2
      = s * N * PL i + QL i := by
    intro i; rw [hPL i, hQL i]; ring
  have hsq := perturb_sq_ne_zero d1 d2 s N hd0
  have hinj := perturb_functional_inj P hS d1 d2 s N PL QL
    (fun i => s * N * PL i + QL i) hPL hQL (fun i => rfl) hsqpos hs1 hNpos hNgt
  exact ⟨d1 - s * N * d2, d2 + s * N * d1, s, N, fun i => s * N * PL i + QL i,
    hFLeq, hsq, hinj, fun i => rfl, hNpos, hNgt, hs⟩

/-- **A convex vertex strictly off a given line.** Given two distinct vertices `a, b`, there is
a convex vertex `w` whose `(v_w − v_a)` has nonzero cross with `(v_b − v_a)` — i.e. `v_w` lies
strictly off the line `v_a v_b`.  Construction: perturb the perpendicular functional
`p(v) = cross(v_b − v_a, v − v_a)` by a large multiple plus the parallel functional, making the
combined integer functional injective on the vertices; its minimiser `w` (convex by
`exists_convex_min`) is forced strictly off the line because some vertex is off it
(`exists_pos_fan_term`) and the large multiple dominates. -/
lemma exists_offline_convex (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (h2 : 2 ≤ P.n) (a b : ZMod P.n) (hne : P.vert a ≠ P.vert b) :
    ∃ w : ZMod P.n, 0 < cornerCross P w ∧
      cross (toReal (P.vert b) - toReal (P.vert a))
        (toReal (P.vert w) - toReal (P.vert a)) ≠ 0 := by
  classical
  set d1 : ℤ := (P.vert b).1 - (P.vert a).1 with hd1def
  set d2 : ℤ := (P.vert b).2 - (P.vert a).2 with hd2def
  set PL : ZMod P.n → ℤ := fun i => -d2 * (P.vert i).1 + d1 * (P.vert i).2 with hPLdef
  set QL : ZMod P.n → ℤ := fun i => d1 * (P.vert i).1 + d2 * (P.vert i).2 with hQLdef
  clear_value d1 d2 PL QL
  -- the difference vector is nonzero, with coordinates `(d1, d2)`
  have hDne : toReal (P.vert b) - toReal (P.vert a) ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hne ((toReal_injective h).symm)
  have hD1 : (toReal (P.vert b) - toReal (P.vert a)).1 = (d1 : ℝ) := by
    simp only [Prod.fst_sub, toReal, hd1def]; push_cast; ring
  have hD2 : (toReal (P.vert b) - toReal (P.vert a)).2 = (d2 : ℝ) := by
    simp only [Prod.snd_sub, toReal, hd2def]; push_cast; ring
  have hd0 : ¬(d1 = 0 ∧ d2 = 0) := by
    rintro ⟨z1, z2⟩
    apply hDne
    apply Prod.ext
    · rw [hD1, z1]; simp
    · rw [hD2, z2]; simp
  -- cross(D, v_i − v_a) = PL i − PL a
  have hcross : ∀ i : ZMod P.n,
      cross (toReal (P.vert b) - toReal (P.vert a)) (toReal (P.vert i) - toReal (P.vert a))
        = (PL i : ℝ) - (PL a : ℝ) := by
    intro i
    simp only [cross, toReal, Prod.fst_sub, Prod.snd_sub, hPLdef, hd1def, hd2def]
    push_cast; ring
  -- a vertex off the line, and the perturbed injective functional
  obtain ⟨t, ht0⟩ := exists_cross_ne P hO a b hne
  have ht : PL t ≠ PL a := by
    intro hEq; apply ht0; rw [hcross t, hEq]; ring
  obtain ⟨c, dc, s, N, FL, hFLeq, hcdR, hFLinj, hFLdef, hNpos, hNgt, hs⟩ :=
    exists_perturbed_functional P hS d1 d2 hd0 PL QL
      (fun i => by simp only [hPLdef]) (fun i => by simp only [hQLdef]) t a ht
  -- minimise the functional
  obtain ⟨w, hw_conv, hw_min⟩ := exists_convex_min P hS hO h2 c dc hcdR (by
    intro i j hij
    apply hFLinj
    have ci : (c : ℝ) * (P.vert i).1 + (dc : ℝ) * (P.vert i).2 = (FL i : ℝ) := by
      rw [← hFLeq i]; push_cast; ring
    have cj : (c : ℝ) * (P.vert j).1 + (dc : ℝ) * (P.vert j).2 = (FL j : ℝ) := by
      rw [← hFLeq j]; push_cast; ring
    rw [ci, cj] at hij; exact_mod_cast hij)
  refine ⟨w, hw_conv, ?_⟩
  rw [hcross w]
  -- PL w ≠ PL a (off the line)
  have hne_pl : PL w ≠ PL a := by
    intro hwa
    have cast_w : (c : ℝ) * (P.vert w).1 + (dc : ℝ) * (P.vert w).2 = (FL w : ℝ) := by
      rw [← hFLeq w]; push_cast; ring
    have cast_t : (c : ℝ) * (P.vert t).1 + (dc : ℝ) * (P.vert t).2 = (FL t : ℝ) := by
      rw [← hFLeq t]; push_cast; ring
    have hmin_t : FL w ≤ FL t := by
      have hh := hw_min t; rw [cast_w, cast_t] at hh; exact_mod_cast hh
    exact perturb_min_off_line s N (PL w) (PL a) (PL t) (QL w) (QL t) hs hNpos (hNgt t w)
      (by rw [← hFLdef w, ← hFLdef t]; exact hmin_t) hwa
  intro hzero
  apply hne_pl
  have : (PL w : ℝ) = (PL a : ℝ) := by linarith [hzero]
  exact_mod_cast this

/-- **Three distinct convex vertices, dodging two prescribed indices.** A simple,
positively-oriented polygon with `≥ 3` vertices has a convex vertex `i` avoiding any two given
indices `e₁, e₂`.  Proof: a generic shear exposes the lowest vertex `a` and the highest vertex
`b` as two distinct convex vertices; `exists_offline_convex` supplies a third convex vertex `w`
strictly off the line `v_a v_b`, hence distinct from both.  Three distinct convex vertices
cannot all lie in the two-element set `{e₁, e₂}`. -/
lemma exists_convex_vertex_avoiding (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) (h3 : 3 ≤ P.n) (e₁ e₂ : ZMod P.n) :
    ∃ i : ZMod P.n, 0 < cornerCross P i ∧ i ≠ e₁ ∧ i ≠ e₂ := by
  have h2 : 2 ≤ P.n := by omega
  haveI : Fact (1 < P.n) := ⟨by omega⟩
  obtain ⟨k₀, hk⟩ := exists_generic_shear P hS
  -- injectivity of the functional `k₀·x + y` (lowest/highest direction)
  have hinj_a : ∀ i j : ZMod P.n,
      (k₀ : ℝ) * (P.vert i).1 + ((1 : ℤ) : ℝ) * (P.vert i).2
        = (k₀ : ℝ) * (P.vert j).1 + ((1 : ℤ) : ℝ) * (P.vert j).2 → i = j := by
    intro i j hij
    by_contra hne
    apply hk i j hne
    have hR : ((P.vert i).2 + k₀ * (P.vert i).1 : ℝ)
        = ((P.vert j).2 + k₀ * (P.vert j).1 : ℝ) := by push_cast at hij ⊢; linarith
    exact_mod_cast hR
  have hinj_b : ∀ i j : ZMod P.n,
      ((-k₀ : ℤ) : ℝ) * (P.vert i).1 + ((-1 : ℤ) : ℝ) * (P.vert i).2
        = ((-k₀ : ℤ) : ℝ) * (P.vert j).1 + ((-1 : ℤ) : ℝ) * (P.vert j).2 → i = j := by
    intro i j hij
    apply hinj_a i j
    push_cast at hij ⊢; linarith
  obtain ⟨a, ha_conv, ha_min⟩ :=
    exists_convex_min P hS hO h2 k₀ 1 (by push_cast; positivity) hinj_a
  obtain ⟨b, hb_conv, hb_min⟩ :=
    exists_convex_min P hS hO h2 (-k₀) (-1) (by push_cast; positivity) hinj_b
  -- `a ≠ b` since `a` minimises and `b` maximises a functional that is not constant
  have hab : a ≠ b := by
    intro hEq
    have hconst : ∀ j : ZMod P.n,
        (k₀ : ℝ) * (P.vert j).1 + ((1 : ℤ) : ℝ) * (P.vert j).2
          = (k₀ : ℝ) * (P.vert a).1 + ((1 : ℤ) : ℝ) * (P.vert a).2 := by
      intro j
      have h1 := ha_min j
      have h2' := hb_min j
      rw [← hEq] at h2'
      push_cast at h1 h2' ⊢; linarith
    have e01 := (hconst 0).trans (hconst 1).symm
    exact zero_ne_one (hinj_a 0 1 e01)
  have hvne : P.vert a ≠ P.vert b := fun h => hab (vert_injective P hS h)
  obtain ⟨w, hw_conv, hw_off⟩ := exists_offline_convex P hS hO h2 a b hvne
  have hwa : w ≠ a := fun h => hw_off (by rw [h, sub_self]; simp [cross])
  have hwb : w ≠ b := fun h => hw_off (by rw [h]; simp only [cross]; ring)
  -- pigeonhole: one of the three distinct convex vertices avoids `{e₁, e₂}`
  by_cases h1 : a ≠ e₁ ∧ a ≠ e₂
  · exact ⟨a, ha_conv, h1.1, h1.2⟩
  by_cases h2' : b ≠ e₁ ∧ b ≠ e₂
  · exact ⟨b, hb_conv, h2'.1, h2'.2⟩
  rw [not_and_or, not_not, not_not] at h1 h2'
  refine ⟨w, hw_conv, ?_, ?_⟩
  · intro hwe
    rcases h1 with hae | hae
    · exact hwa (hwe.trans hae.symm)
    · rcases h2' with hbe | hbe
      · exact hwb (hwe.trans hbe.symm)
      · exact hab (hae.trans hbe.symm)
  · intro hwe
    rcases h1 with hae | hae
    · rcases h2' with hbe | hbe
      · exact hab (hae.trans hbe.symm)
      · exact hwb (hwe.trans hbe.symm)
    · exact hwa (hwe.trans hae.symm)

/-! ### Open-ear interior: the ear-inside linchpin

For an empty ear at apex `vₘ₊₁` of `R` (`R.n = m+2`, `0 < cornerCross R (m+1)`), the open
triangle `T = (vₘ, vₘ₊₁, v₀)` lies off `R.boundary` and carries winding `1`. -/

/-- **First exit over three affine functionals.** If `αⱼ > 0` for all `j` and some
`βⱼ < 0`, there is a parameter `u ∈ (0,1]` at which all three affine values
`(1−u)αⱼ + uβⱼ` are `≥ 0` and one of them is exactly `0` (the first boundary hit). -/
lemma first_exit_affine_three (α β : Fin 3 → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∃ i, β i < 0) :
    ∃ (u : ℝ) (i₀ : Fin 3), 0 < u ∧ u ≤ 1 ∧ (∀ j, 0 ≤ (1 - u) * α j + u * β j)
      ∧ (1 - u) * α i₀ + u * β i₀ = 0 := by
  classical
  set r : Fin 3 → ℝ := fun i => if β i < 0 then α i / (α i - β i) else 2 with hr
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ r ⟨0, Finset.mem_univ 0⟩
  -- there is an index with β < 0 and root < 1, so the minimal root is < 1
  obtain ⟨k, hk⟩ := hβ
  have hrk : r k < 1 := by
    rw [hr]; simp only; rw [if_pos hk]
    rw [div_lt_one (by linarith [hα k])]; linarith
  have hri0_lt : r i₀ < 1 := lt_of_le_of_lt (hmin k (Finset.mem_univ k)) hrk
  -- so β i₀ < 0
  have hbi0 : β i₀ < 0 := by
    by_contra hc; push Not at hc
    rw [hr] at hri0_lt; simp only at hri0_lt; rw [if_neg (not_lt.mpr hc)] at hri0_lt; norm_num at hri0_lt
  set u := r i₀ with hu
  have hupos : 0 < u := by
    rw [hu, hr]; simp only; rw [if_pos hbi0]
    exact div_pos (hα i₀) (by have := hα i₀; linarith)
  refine ⟨u, i₀, hupos, le_of_lt hri0_lt, ?_, ?_⟩
  · intro j
    by_cases hbj : β j < 0
    · have hule : u ≤ α j / (α j - β j) := by
        have := hmin j (Finset.mem_univ j); rw [hr] at this; simp only at this; rwa [if_pos hbj] at this
      have hden : 0 < α j - β j := by linarith [hα j]
      rw [le_div_iff₀ hden] at hule; nlinarith
    · push Not at hbj
      have : 0 ≤ (1 - u) * α j := mul_nonneg (by linarith [hri0_lt]) (hα j).le
      have : 0 ≤ u * β j := mul_nonneg hupos.le hbj
      nlinarith [mul_nonneg (by linarith [hri0_lt] : (0:ℝ) ≤ 1 - u) (hα j).le]
  · rw [hu, hr]; simp only; rw [if_pos hbi0]
    have hden : α i₀ - β i₀ ≠ 0 := ne_of_gt (by have := hα i₀; linarith)
    field_simp; ring

/-- A cross functional is affine along a segment (restated, public). -/
lemma cross_affine_seg_pk (u w e0 e1 : ℝ × ℝ) (s : ℝ) :
    cross u (((1 - s) • e0 + s • e1) - w)
      = (1 - s) * cross u (e0 - w) + s * cross u (e1 - w) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- The three sub-triangle cross areas at `z` sum to the total signed area (restated). -/
lemma cross_bary_sum_pk (a b c z : ℝ × ℝ) :
    cross (b - a) (z - a) + cross (c - b) (z - b) + cross (a - c) (z - c)
      = cross (b - a) (c - a) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- A closed-triangle point on the line `a–b` lies on `[a,b]` (restated, public). -/
lemma mem_seg_ab_pk (a b c z : ℝ × ℝ)
    (hD : 0 < cross (b - a) (c - a)) (hz : inTriangle a b c z)
    (hf1 : cross (b - a) (z - a) = 0) : z ∈ segment ℝ a b := by
  obtain ⟨_, hf2, hf3⟩ := hz
  set D := cross (b - a) (c - a) with hDdef
  set r := cross (a - c) (z - c) / D with hrdef
  have hr0 : 0 ≤ r := div_nonneg hf3 hD.le
  have hsum := cross_bary_sum_pk a b c z
  rw [hf1] at hsum
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hD]; nlinarith [hf2]
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  have heq1 : (z.1 - a.1) * D = cross (a - c) (z - c) * (b.1 - a.1) := by
    have := hf1; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (c.1 - a.1) * this
  have heq2 : (z.2 - a.2) * D = cross (a - c) (z - c) * (b.2 - a.2) := by
    have := hf1; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (c.2 - a.2) * this
  have hDne : D ≠ 0 := ne_of_gt hD
  apply Prod.ext
  · show ((1 - r) • a + r • b).1 = z.1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; rw [hrdef]; field_simp; linarith [heq1]
  · show ((1 - r) • a + r • b).2 = z.2
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [hrdef]; field_simp; linarith [heq2]

/-- A closed-triangle point on the line `b–c` lies on `[b,c]` (restated, public). -/
lemma mem_seg_bc_pk (a b c z : ℝ × ℝ)
    (hD : 0 < cross (b - a) (c - a)) (hz : inTriangle a b c z)
    (hf2 : cross (c - b) (z - b) = 0) : z ∈ segment ℝ b c := by
  obtain ⟨hf1, _, hf3⟩ := hz
  set D := cross (b - a) (c - a) with hDdef
  set r := cross (b - a) (z - a) / D with hrdef
  have hr0 : 0 ≤ r := div_nonneg hf1 hD.le
  have hsum := cross_bary_sum_pk a b c z
  rw [hf2] at hsum
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hD]; nlinarith [hf3]
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  have heq1 : (z.1 - b.1) * D = cross (b - a) (z - a) * (c.1 - b.1) := by
    have := hf2; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (a.1 - b.1) * this
  have heq2 : (z.2 - b.2) * D = cross (b - a) (z - a) * (c.2 - b.2) := by
    have := hf2; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (a.2 - b.2) * this
  have hDne : D ≠ 0 := ne_of_gt hD
  apply Prod.ext
  · show ((1 - r) • b + r • c).1 = z.1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; rw [hrdef]; field_simp; linarith [heq1]
  · show ((1 - r) • b + r • c).2 = z.2
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [hrdef]; field_simp; linarith [heq2]

/-- A closed-triangle point on the line `c–a` lies on `[c,a]`. -/
lemma mem_seg_ca_pk (a b c z : ℝ × ℝ)
    (hD : 0 < cross (b - a) (c - a)) (hz : inTriangle a b c z)
    (hf3 : cross (a - c) (z - c) = 0) : z ∈ segment ℝ c a := by
  obtain ⟨hf1, hf2, _⟩ := hz
  set D := cross (b - a) (c - a) with hDdef
  set r := cross (c - b) (z - b) / D with hrdef
  have hr0 : 0 ≤ r := div_nonneg hf2 hD.le
  have hsum := cross_bary_sum_pk a b c z
  rw [hf3] at hsum
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hD]; nlinarith [hf1]
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  have heq1 : (z.1 - c.1) * D = cross (c - b) (z - b) * (a.1 - c.1) := by
    have := hf3; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (b.1 - c.1) * this
  have heq2 : (z.2 - c.2) * D = cross (c - b) (z - b) * (a.2 - c.2) := by
    have := hf3; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (b.2 - c.2) * this
  have hDne : D ≠ 0 := ne_of_gt hD
  apply Prod.ext
  · show ((1 - r) • c + r • a).1 = z.1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; rw [hrdef]; field_simp; linarith [heq1]
  · show ((1 - r) • c + r • a).2 = z.2
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [hrdef]; field_simp; linarith [heq2]

/-- **A segment from a strict-interior point to an outside point meets a triangle edge.**
If `p` is strictly inside the CCW triangle `(a,b,c)` and `e ∉ inTriangle a b c`, then the
segment `[p,e]` meets one of the three closed edges `[a,b]`, `[b,c]`, `[c,a]`. -/
lemma seg_meets_triangle_boundary (a b c p e : ℝ × ℝ)
    (hD : 0 < cross (b - a) (c - a))
    (hp1 : 0 < cross (b - a) (p - a)) (hp2 : 0 < cross (c - b) (p - b))
    (hp3 : 0 < cross (a - c) (p - c)) (he : ¬ inTriangle a b c e) :
    (∃ z ∈ segment ℝ p e, z ∈ segment ℝ a b) ∨
    (∃ z ∈ segment ℝ p e, z ∈ segment ℝ b c) ∨
    (∃ z ∈ segment ℝ p e, z ∈ segment ℝ c a) := by
  classical
  set α : Fin 3 → ℝ := ![cross (b - a) (p - a), cross (c - b) (p - b), cross (a - c) (p - c)] with hαdef
  set β : Fin 3 → ℝ := ![cross (b - a) (e - a), cross (c - b) (e - b), cross (a - c) (e - c)] with hβdef
  have hαpos : ∀ i, 0 < α i := by
    intro i; fin_cases i <;> simp only [hαdef]
    · exact hp1
    · exact hp2
    · exact hp3
  have hβneg : ∃ i, β i < 0 := by
    by_contra hc; push Not at hc
    apply he
    refine ⟨?_, ?_, ?_⟩
    · have := hc 0; simpa [hβdef] using this
    · have := hc 1; simpa [hβdef] using this
    · have := hc 2; simpa [hβdef] using this
  obtain ⟨u, i₀, hupos, hule, hall, hzero⟩ := first_exit_affine_three α β hαpos hβneg
  set z := (1 - u) • p + u • e with hzdef
  have hseg : z ∈ segment ℝ p e := ⟨1 - u, u, by linarith, hupos.le, by ring, by rw [hzdef]⟩
  have hf : ∀ i : Fin 3, (fun (w v : ℝ × ℝ) => cross w v)
      (![b - a, c - b, a - c] i) (z - ![a, b, c] i)
      = (1 - u) * α i + u * β i := by
    intro i
    fin_cases i <;> simp only [hzdef, hαdef, hβdef] <;>
      exact cross_affine_seg_pk _ _ _ _ _
  have hz1 : cross (b - a) (z - a) = (1 - u) * α 0 + u * β 0 := by
    have := hf 0; simpa using this
  have hz2 : cross (c - b) (z - b) = (1 - u) * α 1 + u * β 1 := by
    have := hf 1; simpa using this
  have hz3 : cross (a - c) (z - c) = (1 - u) * α 2 + u * β 2 := by
    have := hf 2; simpa using this
  have hzT : inTriangle a b c z := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hz1]; exact hall 0
    · rw [hz2]; exact hall 1
    · rw [hz3]; exact hall 2
  fin_cases i₀
  · left; refine ⟨z, hseg, mem_seg_ab_pk a b c z hD hzT ?_⟩
    rw [hz1]; simpa using hzero
  · right; left; refine ⟨z, hseg, mem_seg_bc_pk a b c z hD hzT ?_⟩
    rw [hz2]; simpa using hzero
  · right; right; refine ⟨z, hseg, mem_seg_ca_pk a b c z hD hzT ?_⟩
    rw [hz3]; simpa using hzero

/-- **The far endpoint is not on the near sub-segment.** If `p` is strictly between
`x` and `y` (`p ∈ openSegment ℝ x y`) and `x ≠ y`, then `x ∉ segment ℝ p y`. -/
lemma corner_notMem_segment {x y p : ℝ × ℝ} (hp : p ∈ openSegment ℝ x y) (hxy : x ≠ y) :
    x ∉ segment ℝ p y := by
  rintro ⟨s1, s2, hs1, hs2, hs12, hxeq⟩
  obtain ⟨t1, t2, ht1, ht2, ht12, hpeq⟩ := hp
  -- x = (s1 t1) • x + (s1 t2 + s2) • y
  have hx1 : x.1 = (s1 * t1) * x.1 + (s1 * t2 + s2) * y.1 := by
    have h1 : x.1 = s1 * p.1 + s2 * y.1 := by
      have := congrArg Prod.fst hxeq
      simpa [Prod.fst_add, Prod.smul_fst, smul_eq_mul] using this.symm
    have h2 : p.1 = t1 * x.1 + t2 * y.1 := by
      have := congrArg Prod.fst hpeq
      simpa [Prod.fst_add, Prod.smul_fst, smul_eq_mul] using this.symm
    rw [h2] at h1; linear_combination h1
  have hx2 : x.2 = (s1 * t1) * x.2 + (s1 * t2 + s2) * y.2 := by
    have h1 : x.2 = s1 * p.2 + s2 * y.2 := by
      have := congrArg Prod.snd hxeq
      simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using this.symm
    have h2 : p.2 = t1 * x.2 + t2 * y.2 := by
      have := congrArg Prod.snd hpeq
      simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using this.symm
    rw [h2] at h1; linear_combination h1
  -- coefficient of x is s1*t1, which sums with the y-coefficient to 1
  have hsum : s1 * t1 + (s1 * t2 + s2) = 1 := by nlinarith [hs12, ht12]
  -- (1 - s1 t1) (x - y) = 0 in each coordinate
  have hc1 : (1 - s1 * t1) * (x.1 - y.1) = 0 := by linear_combination hx1 + y.1 * hsum
  have hc2 : (1 - s1 * t1) * (x.2 - y.2) = 0 := by linear_combination hx2 + y.2 * hsum
  -- x ≠ y in some coordinate
  have hxy' : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
    by_contra hcc; push Not at hcc; exact hxy (Prod.ext hcc.1 hcc.2)
  have hlam : s1 * t1 = 1 := by
    rcases hxy' with h | h
    · have : 1 - s1 * t1 = 0 := by
        rcases mul_eq_zero.mp hc1 with hh | hh
        · exact hh
        · exact absurd (sub_eq_zero.mp hh) h
      linarith
    · have : 1 - s1 * t1 = 0 := by
        rcases mul_eq_zero.mp hc2 with hh | hh
        · exact hh
        · exact absurd (sub_eq_zero.mp hh) h
      linarith
  -- but s1 ≤ 1 and t1 < 1, so s1 t1 < 1
  have ht1lt : t1 < 1 := by linarith
  have hs1le : s1 ≤ 1 := by linarith
  nlinarith [hlam, ht1, ht2, hs1, hs2, ht1lt, hs1le]

/-- A point of a closed segment distinct from both endpoints lies in the open segment. -/
lemma mem_openSegment_of_ne_ends {a c p : ℝ × ℝ}
    (h : p ∈ segment ℝ a c) (h1 : p ≠ a) (h2 : p ≠ c) : p ∈ openSegment ℝ a c := by
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := h
  refine ⟨x, y, ?_, ?_, hxy, hp⟩
  · rcases eq_or_lt_of_le hx with he | he
    · exfalso; apply h2; rw [← hp, ← he]; simp; rw [show y = 1 by linarith]; simp
    · exact he
  · rcases eq_or_lt_of_le hy with he | he
    · exfalso; apply h1; rw [← hp, ← he]; simp; rw [show x = 1 by linarith]; simp
    · exact he

/-- The open ear triangle `int(T)`, `T = (vₘ, vₘ₊₁, v₀)`: the strict interior — points
strictly to the left of each of the three directed triangle edges. Convex (intersection
of three open half-planes). -/
def openEar (R : LatticePolygon) (m : ℕ) : Set (ℝ × ℝ) :=
  {q | 0 < cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
         (q - toReal (R.vert (m : ZMod R.n)))
     ∧ 0 < cross (toReal (R.vert 0) - toReal (R.vert ((m : ZMod R.n) + 1)))
         (q - toReal (R.vert ((m : ZMod R.n) + 1)))
     ∧ 0 < cross (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0))
         (q - toReal (R.vert 0))}

/-- `openEar` is convex. -/
lemma openEar_convex (R : LatticePolygon) (m : ℕ) : Convex ℝ (openEar R m) := by
  have h1 := convex_pos_cross (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert ((m : ZMod R.n) + 1)))
  have h2 := convex_pos_cross (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0))
  have h3 := convex_pos_cross (toReal (R.vert 0)) (toReal (R.vert (m : ZMod R.n)))
  exact h1.inter (h2.inter h3)

/-- On the open ear, the ear triangle's winding is `1`. -/
lemma openEar_winding_one (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2)
    {q : ℝ × ℝ} (hq : q ∈ openEar R m) : (earTri R m hm).winding q = 1 := by
  obtain ⟨hf1, hf2, hf3⟩ := hq
  refine winding_eq_one_of_three_cross_pos_real (earTri R m hm) rfl q ?_
  intro j
  have key : ∀ (x y : ℝ × ℝ), 0 < cross (y - x) (q - x) → 0 < cross (x - q) (y - q) := by
    intro x y h
    rwa [show cross (x - q) (y - q) = cross (y - x) (q - x) by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring]
  fin_cases j
  · exact key _ _ hf1
  · exact key _ _ hf2
  · exact key _ _ hf3

/-- **The open ear is nonempty.** The apex `vₘ₊₁` is a convex corner
(`0 < cornerCross R (m+1)`), so the ear triangle `(vₘ, vₘ₊₁, v₀)` has strictly positive
signed area; its centroid `(vₘ + vₘ₊₁ + v₀)/3` lies strictly to the left of all three
directed edges (each cross equals `⅓` of the corner cross), hence sits in `openEar R m`.
Reusable: gives the witness needed to upgrade the open-ear constancy lemmas to genuine
existentials. -/
lemma openEar_nonempty (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) : (openEar R m).Nonempty := by
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  have hcc : 0 < cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert (0 : ZMod R.n)) - toReal (R.vert ((m : ZMod R.n) + 1))) := by
    have h := hear.1
    unfold cornerCross at h
    rwa [show ((m : ZMod R.n) + 1 - 1) = (m : ZMod R.n) by ring, hmp1mp1] at h
  set a := toReal (R.vert (m : ZMod R.n)) with ha
  set b := toReal (R.vert ((m : ZMod R.n) + 1)) with hb
  set c := toReal (R.vert (0 : ZMod R.n)) with hc
  refine ⟨((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3), ?_, ?_, ?_⟩
  · have e : cross (b - a) (((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3) - a)
        = (1 / 3) * cross (b - a) (c - b) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; linarith [hcc]
  · have e : cross (c - b) (((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3) - b)
        = (1 / 3) * cross (b - a) (c - b) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; linarith [hcc]
  · have e : cross (a - c) (((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3) - c)
        = (1 / 3) * cross (b - a) (c - b) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; linarith [hcc]

/-- A point of a segment `[a,b]` lies on the line through `a,b`: `cross (b-a) (q-a) = 0`. -/
lemma cross_seg_zero (a b q' : ℝ × ℝ) (h : q' ∈ segment ℝ a b) :
    cross (b - a) (q' - a) = 0 := by
  obtain ⟨u, v, _, _, huv, rfl⟩ := h
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show u = 1 - v by linarith]; ring

/-- **Task 1: the open ear lies off `R.boundary`.** For an empty ear at apex `vₘ₊₁`
(`0 < cornerCross R (m+1)`, `m ≥ 2`), the open triangle `int(T)` avoids every edge of
`R`: the two legs by the strict half-plane test, the remaining edges by
empty-ear/diagonal disjointness and `R`-simplicity. -/
lemma open_ear_subset_compl_boundary (R : LatticePolygon) (hS : R.IsSimple)
    (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    openEar R m ⊆ R.boundaryᶜ := by
  classical
  haveI : NeZero R.n := ⟨by omega⟩
  haveI : Fact (1 < R.n) := ⟨by omega⟩
  intro q hq hqb
  obtain ⟨hf1, hf2, hf3⟩ := hq
  set a := toReal (R.vert (m : ZMod R.n)) with ha
  set b := toReal (R.vert ((m : ZMod R.n) + 1)) with hb
  set c := toReal (R.vert 0) with hc
  have hbase := earTri_cross_base_pos R m hm hear
  have hqT : inTriangle a b c q := ⟨hf1.le, hf2.le, hf3.le⟩
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  have hmm1 : (m : ZMod R.n) - 1 = ((m - 1 : ℕ) : ZMod R.n) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hval : ∀ j : ℕ, j < R.n → ((j : ZMod R.n)).val = j := fun j hj => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj]
  have hmne0 : (m : ZMod R.n) ≠ 0 := by
    intro he; have := congrArg ZMod.val he; rw [hval m (by omega), ZMod.val_zero] at this; omega
  have h1ne0 : (1 : ZMod R.n) ≠ 0 := one_ne_zero
  have h1nem : (1 : ZMod R.n) ≠ (m : ZMod R.n) := by
    intro he; have := congrArg ZMod.val he
    rw [ZMod.val_one, hval m (by omega)] at this; omega
  have h1nemp1 : (1 : ZMod R.n) ≠ (m : ZMod R.n) + 1 := by
    intro he; apply hmne0; linear_combination -he
  have hmp1_ne_0 : (m : ZMod R.n) + 1 ≠ 0 := by
    intro he; apply h1ne0; rw [← hmp1mp1, he, zero_add]
  -- empty-ear: foreign vertices are outside the closed triangle
  have hforeign : ∀ j : ZMod R.n, j ≠ (m : ZMod R.n) → j ≠ (m : ZMod R.n) + 1 → j ≠ 0 →
      ¬ inTriangle a b c (toReal (R.vert j)) := by
    intro j hjm hjmp1 hj0
    have := hear.2 j (by rw [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring]; exact hjm)
      hjmp1 (by rw [hmp1mp1]; exact hj0)
    rwa [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring, hmp1mp1] at this
  have hqa : q ≠ a := by
    intro he; rw [he, show cross (b - a) (a - a) = 0 by rw [sub_self, cross]; simp] at hf1
    exact lt_irrefl _ hf1
  have hqc : q ≠ c := by
    intro he; rw [he, show cross (a - c) (c - c) = 0 by rw [sub_self, cross]; simp] at hf3
    exact lt_irrefl _ hf3
  have hqforeign : ∀ j : ZMod R.n, j ≠ (m : ZMod R.n) → j ≠ (m : ZMod R.n) + 1 → j ≠ 0 →
      q ≠ toReal (R.vert j) := fun j hjm hjmp1 hj0 he => hforeign j hjm hjmp1 hj0 (he ▸ hqT)
  rw [LatticePolygon.boundary, Set.mem_iUnion] at hqb
  obtain ⟨k, hk⟩ := hqb
  have hkseg : q ∈ segment ℝ (toReal (R.vert k)) (toReal (R.vert (k + 1))) := hk
  have hlegM : segment ℝ a b = R.edgeSeg (m : ZMod R.n) := by rw [LatticePolygon.edgeSeg]
  have hlegMp1 : segment ℝ b c = R.edgeSeg ((m : ZMod R.n) + 1) := by
    rw [LatticePolygon.edgeSeg, hmp1mp1]
  by_cases hkm : k = (m : ZMod R.n)
  · rw [LatticePolygon.edgeSeg, hkm] at hk
    exact (ne_of_gt hf1) (cross_seg_zero a b q hk)
  by_cases hkmp1 : k = (m : ZMod R.n) + 1
  · rw [LatticePolygon.edgeSeg, hkmp1, hmp1mp1] at hk
    exact (ne_of_gt hf2) (cross_seg_zero b c q hk)
  -- non-leg edge k.  Generic facts about its endpoints.
  have hq_vk : q ≠ toReal (R.vert k) := by
    by_cases hk0' : k = 0
    · rw [hk0']; exact hqc
    · exact hqforeign k hkm hkmp1 hk0'
  have hq_vk1 : q ≠ toReal (R.vert (k + 1)) := by
    by_cases hkm1' : k = (m : ZMod R.n) - 1
    · have hks : k + 1 = (m : ZMod R.n) := by rw [hkm1']; ring
      rw [hks]; exact hqa
    · refine hqforeign (k + 1) (fun he => hkm1' (by linear_combination he))
        (fun he => hkm (by linear_combination he)) (fun he => hkmp1 ?_)
      rw [show (m : ZMod R.n) + 1 = ((m : ZMod R.n) + 1 + 1) - 1 by ring, hmp1mp1]
      linear_combination he
  have hvne : toReal (R.vert k) ≠ toReal (R.vert (k + 1)) := fun he => hS.1 k (toReal_injective he)
  have hqopen : q ∈ openSegment ℝ (toReal (R.vert k)) (toReal (R.vert (k + 1))) :=
    mem_openSegment_of_ne_ends hkseg hq_vk hq_vk1
  have hsubL : segment ℝ q (toReal (R.vert k)) ⊆ R.edgeSeg k :=
    (convex_segment _ _).segment_subset hkseg (left_mem_segment _ _ _)
  have hsubR : segment ℝ q (toReal (R.vert (k + 1))) ⊆ R.edgeSeg k :=
    (convex_segment _ _).segment_subset hkseg (right_mem_segment _ _ _)
  by_cases hk0 : k = 0
  · -- edge 0 = [v₀ = c, v₁]; foreign endpoint v₁ = v_{k+1}
    have hef : ¬ inTriangle a b c (toReal (R.vert (k + 1))) := by
      have hks : k + 1 = 1 := by rw [hk0, zero_add]
      rw [hks]; exact hforeign 1 h1nem h1nemp1 h1ne0
    rcases seg_meets_triangle_boundary a b c q (toReal (R.vert (k + 1))) hbase hf1 hf2 hf3 hef with
      ⟨z, hzqe, hzt⟩ | ⟨z, hzqe, hzt⟩ | ⟨z, hzqe, hzt⟩
    · -- z ∈ [a,b] = edge m ; edge 0 disjoint from edge m
      have hd : Disjoint (R.edgeSeg k) (R.edgeSeg (m : ZMod R.n)) :=
        hS.2.1 k (m : ZMod R.n) hkm (by rw [hk0, zero_add]; exact h1nem)
          (fun he => hkmp1 he.symm)
      exact Set.disjoint_left.mp hd (hsubR hzqe) (hlegM ▸ hzt)
    · -- z ∈ [b,c] = edge (m+1) ; (edge (m+1)) ∩ (edge 0) = {v_0}
      have hint := hS.2.2 ((m : ZMod R.n) + 1)
      rw [hmp1mp1] at hint
      have hmem : z ∈ R.edgeSeg ((m : ZMod R.n) + 1) ∩ R.edgeSeg 0 :=
        ⟨hlegMp1 ▸ hzt, hk0 ▸ hsubR hzqe⟩
      rw [hint] at hmem
      have hzc : z = toReal (R.vert k) := by rw [hk0]; simpa using hmem
      exact corner_notMem_segment hqopen hvne (hzc ▸ hzqe)
    · -- z ∈ [c,a] = D ; D ∩ (edge 0) = {v_0}
      have hD := diag_adjNext_inter R hS m hm hm2 hear
      have hz0 : z ∈ R.edgeSeg 0 := hk0 ▸ hsubR hzqe
      rw [LatticePolygon.edgeSeg, zero_add] at hz0
      have hmem : z ∈ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
          ∩ segment ℝ (toReal (R.vert 0)) (toReal (R.vert 1)) :=
        ⟨by rw [segment_symm]; exact hzt, hz0⟩
      rw [hD] at hmem
      have hzc : z = toReal (R.vert k) := by rw [hk0]; simpa using hmem
      exact corner_notMem_segment hqopen hvne (hzc ▸ hzqe)
  by_cases hkm1 : k = (m : ZMod R.n) - 1
  · -- edge (m-1) = [v_{m-1} = v_k, v_m = a = v_{k+1}]; foreign endpoint v_k
    have hk1succ : k + 1 = (m : ZMod R.n) := by rw [hkm1]; ring
    have hqopen' : q ∈ openSegment ℝ (toReal (R.vert (k + 1))) (toReal (R.vert k)) := by
      rw [openSegment_symm]; exact hqopen
    have hef : ¬ inTriangle a b c (toReal (R.vert k)) := hforeign k hkm hkmp1 hk0
    rcases seg_meets_triangle_boundary a b c q (toReal (R.vert k)) hbase hf1 hf2 hf3 hef with
      ⟨z, hzqe, hzt⟩ | ⟨z, hzqe, hzt⟩ | ⟨z, hzqe, hzt⟩
    · -- z ∈ [a,b] = edge m ; (edge (m-1)) ∩ (edge m) = {a = v_{k+1}}
      have hadj : R.edgeSeg k ∩ R.edgeSeg (k + 1) = {toReal (R.vert (k + 1))} := hS.2.2 k
      have hza : z = toReal (R.vert (k + 1)) := by
        have : z ∈ ({toReal (R.vert (k + 1))} : Set (ℝ × ℝ)) := by
          rw [← hadj]; exact ⟨hsubL hzqe, by rw [hk1succ]; exact hlegM ▸ hzt⟩
        simpa using this
      exact corner_notMem_segment hqopen' hvne.symm (hza ▸ hzqe)
    · -- z ∈ [b,c] = edge (m+1) ; (edge (m-1)) ∩ (edge (m+1)) = ∅
      have hd : Disjoint (R.edgeSeg k) (R.edgeSeg ((m : ZMod R.n) + 1)) :=
        hS.2.1 k ((m : ZMod R.n) + 1) hkmp1
          (by rw [hk1succ]; exact fun he => h1ne0 (by linear_combination -he))
          (by rw [hmp1mp1]; exact fun he => hk0 he.symm)
      exact Set.disjoint_left.mp hd (hsubL hzqe) (hlegMp1 ▸ hzt)
    · -- z ∈ [c,a] = D ; D ∩ (edge (m-1)) = {v_m}
      have hD := diag_adjPrev_inter R hS m hm hm2 hear
      have hzedge : z ∈ R.edgeSeg k := hsubL hzqe
      rw [LatticePolygon.edgeSeg, show k = ((m - 1 : ℕ) : ZMod R.n) by rw [← hmm1, hkm1]] at hzedge
      have hzedge' : z ∈ segment ℝ (toReal (R.vert ((m - 1 : ℕ) : ZMod R.n)))
          (toReal (R.vert (m : ZMod R.n))) := by
        rw [show ((m - 1 : ℕ) : ZMod R.n) + 1 = (m : ZMod R.n) by rw [← hmm1]; ring] at hzedge
        exact hzedge
      have hmem : z ∈ segment ℝ (toReal (R.vert ((m - 1 : ℕ) : ZMod R.n)))
            (toReal (R.vert (m : ZMod R.n)))
          ∩ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) :=
        ⟨hzedge', by rw [segment_symm]; exact hzt⟩
      rw [hD] at hmem
      have hza : z = toReal (R.vert (k + 1)) := by rw [hk1succ]; simpa using hmem
      exact corner_notMem_segment hqopen' hvne.symm (hza ▸ hzqe)
  · -- generic non-incident edge: both endpoints foreign, all three triangle edges disjoint
    have hkp1_ne_m : k + 1 ≠ (m : ZMod R.n) := fun he => hkm1 (by linear_combination he)
    have hkp1_ne_mp1 : k + 1 ≠ (m : ZMod R.n) + 1 := fun he => hkm (by linear_combination he)
    have hkp1_ne_0 : k + 1 ≠ 0 := fun he => hkmp1 (by
      rw [show (m : ZMod R.n) + 1 = ((m : ZMod R.n) + 1 + 1) - 1 by ring, hmp1mp1]
      linear_combination he)
    have hef : ¬ inTriangle a b c (toReal (R.vert k)) := hforeign k hkm hkmp1 hk0
    rcases seg_meets_triangle_boundary a b c q (toReal (R.vert k)) hbase hf1 hf2 hf3 hef with
      ⟨z, hzqe, hzt⟩ | ⟨z, hzqe, hzt⟩ | ⟨z, hzqe, hzt⟩
    · have hd : Disjoint (R.edgeSeg k) (R.edgeSeg (m : ZMod R.n)) :=
        hS.2.1 k (m : ZMod R.n) hkm hkp1_ne_m (fun he => hkmp1 he.symm)
      exact Set.disjoint_left.mp hd (hsubL hzqe) (hlegM ▸ hzt)
    · have hd : Disjoint (R.edgeSeg k) (R.edgeSeg ((m : ZMod R.n) + 1)) :=
        hS.2.1 k ((m : ZMod R.n) + 1) hkmp1 hkp1_ne_mp1 (by rw [hmp1mp1]; exact fun he => hk0 he.symm)
      exact Set.disjoint_left.mp hd (hsubL hzqe) (hlegMp1 ▸ hzt)
    · have hD := diag_disjoint_nonincident_edge R hS m hm hm2 hear k hkm1 hkm hkmp1 hk0
      have hzac : z ∈ segment ℝ a c := by rw [segment_symm]; exact hzt
      exact Set.disjoint_left.mp hD hzac (hsubL hzqe)

/-- **Winding is constant on the open ear.** `int(T)` is convex (hence preconnected) and
lies off `R.boundary` (`open_ear_subset_compl_boundary`), so `R.winding` takes a single
value on it. -/
lemma winding_const_on_openEar (R : LatticePolygon) (hS : R.IsSimple)
    (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) {p q : ℝ × ℝ}
    (hp : p ∈ openEar R m) (hq : q ∈ openEar R m) : R.winding p = R.winding q :=
  winding_const_of_isPreconnected R
    (open_ear_subset_compl_boundary R hS m hm hm2 hear)
    (openEar_convex R m).isPreconnected hp hq

/-- **The winding `= 1` witness propagates over the whole open ear.** Given a single
off-boundary witness `q*` in `openEar R m` with `R.winding q* = 1`, the constancy of
`R.winding` on the connected open ear (`winding_const_on_openEar`) upgrades it to all
of `openEar`. This is the constancy half of `winding_one_on_open_ear`; the remaining
content is producing the witness. -/
lemma winding_one_on_open_ear_of_witness (R : LatticePolygon) (hS : R.IsSimple)
    (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1))
    (hwit : ∃ q ∈ openEar R m, R.winding q = 1) :
    ∀ q ∈ openEar R m, R.winding q = 1 := by
  obtain ⟨q0, hq0, hq0w⟩ := hwit
  intro q hq
  rw [winding_const_on_openEar R hS m hm hm2 hear hq hq0]; exact hq0w

/-- **The open ear lies off the clip's boundary.** The clip `deleteLast R` has boundary
contained in `R.boundary ∪ D` (`boundary_deleteLast_union_earTri`, `D` the diagonal
`vₘ → v₀`). The open ear avoids `R.boundary` (`open_ear_subset_compl_boundary`) and avoids
`D` (it sits strictly on the apex side of the line `v₀ vₘ`, by its third defining strict
inequality). Hence `openEar ⊆ (deleteLast R).boundaryᶜ`. Clean, reusable: this places the
open ear off the clip boundary so the clip's winding is locally constant on it. -/
lemma openEar_subset_clip_compl_boundary (R : LatticePolygon) (hS : R.IsSimple)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    openEar R m ⊆ (deleteLast R h2).boundaryᶜ := by
  intro q hq hqc
  have hsub : q ∈ R.boundary ∪
      segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := by
    rw [← boundary_deleteLast_union_earTri R h2 m hm]; exact Or.inl hqc
  rcases hsub with hR | hD
  · exact open_ear_subset_compl_boundary R hS m hm hm2 hear hq hR
  · obtain ⟨_, _, hf3⟩ := hq
    have hq0m : q ∈ segment ℝ (toReal (R.vert 0)) (toReal (R.vert (m : ZMod R.n))) := by
      rw [segment_symm]; exact hD
    have hz := cross_seg_zero (toReal (R.vert 0)) (toReal (R.vert (m : ZMod R.n))) q hq0m
    rw [hz] at hf3
    exact absurd hf3 (lt_irrefl 0)

/-- **Reduction of the open-ear witness to a clip-winding-zero witness.** Since the
ear triangle's winding is `1` on the open ear (`openEar_winding_one`) and winding is
additive across the diagonal (`R.winding = clip.winding + earTri.winding`), a point of
the open ear with `(deleteLast R).winding = 0` is exactly a point with `R.winding = 1`.
This packages the Hopf-free reduction `exists_witness_openEar ⟸
(∃ q ∈ openEar, (deleteLast R).winding q = 0)`. -/
lemma exists_witness_openEar_of_clip_zero (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2)
    (hz : ∃ q ∈ openEar R m, (deleteLast R h2).winding q = 0) :
    ∃ q ∈ openEar R m, R.winding q = 1 := by
  obtain ⟨q, hq, hqz⟩ := hz
  refine ⟨q, hq, ?_⟩
  rw [winding_eq_deleteLast_add_earTri R h2 m hm q, hqz, openEar_winding_one R m hm hq]
  norm_num

/-- **The open ear carries clip-winding `0` (the linchpin).** At any point `g` of the
open ear, the ear-triangle winding is `1` (`openEar_winding_one`) and winding is additive
across the diagonal (`R.winding g = (deleteLast R).winding g + (earTri R).winding g`), so
`R.winding g = (deleteLast R).winding g + 1`. Both `R` and the clip `deleteLast R` are
simple and positively oriented (the latter via the `hdS`/`hdO` conjuncts already supplied
by the ear-clipping bundle `validEarLast_of_ear`), so `winding_zero_or_one` pins each of
`R.winding g` and `(deleteLast R).winding g` into `{0,1}`. The only integer solution of
`x = y + 1` with `x, y ∈ {0,1}` is `y = 0`. Hopf-free and non-circular: it uses the
already-discharged clip simplicity/orientation, not any Jordan/exterior connectivity. -/
lemma exists_clip_winding_zero_openEar (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1))
    (hdS : (deleteLast R h2).IsSimple)
    (hdO : (deleteLast R h2).PositivelyOriented) :
    ∃ q ∈ openEar R m, (deleteLast R h2).winding q = 0 := by
  obtain ⟨g, hg⟩ := openEar_nonempty R m hm hear
  refine ⟨g, hg, ?_⟩
  have hgRb : g ∉ R.boundary := open_ear_subset_compl_boundary R hS m hm hm2 hear hg
  have hgCb : g ∉ (deleteLast R h2).boundary :=
    openEar_subset_clip_compl_boundary R hS h2 m hm hm2 hear hg
  have hR01 : R.winding g = 0 ∨ R.winding g = 1 := winding_zero_or_one R hS hO g hgRb
  have hC01 : (deleteLast R h2).winding g = 0 ∨ (deleteLast R h2).winding g = 1 :=
    winding_zero_or_one (deleteLast R h2) hdS hdO g hgCb
  have hear1 : (earTri R m hm).winding g = 1 := openEar_winding_one R m hm hg
  have hsum : R.winding g = (deleteLast R h2).winding g + (earTri R m hm).winding g :=
    winding_eq_deleteLast_add_earTri R h2 m hm g
  rw [hear1] at hsum
  omega

/-- **Step 1 of the unconditional open-ear route — winding is constant on the inside
half-tube `L`.** `L = (⋃ leftRegion i εreg) ∪ (⋃ capB i capR)` is the left-side collar built
in the JCT `compl_boundary_atMost_two` proof: it is path-connected
(`isPathConnected_region_cap_cycle` glued by the corner meets `leftRegion_meet_capB`,
`capB_meet_leftRegion_succ`) and off-boundary (`left_half_subset_compl_boundary`). Hence
`winding_const_of_isPreconnected` makes `P.winding` a single value on the whole of `L`.
For a positively-oriented polygon `leftNormal` points into the interior, so `L` is the
*inside* collar; this is the anchor set carrying the interior winding value `1`. -/
lemma winding_const_on_leftTube (hsimple : P.IsSimple) {εreg capR : ℝ}
    (hεregpos : 0 < εreg) (hcapRpos : 0 < capR) (hcapRfs : capR ≤ P.featureSize)
    {p q : ℝ × ℝ}
    (hp : p ∈ (⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR))
    (hq : q ∈ (⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR)) :
    P.winding p = P.winding q := by
  have hLpc : IsPathConnected ((⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR)) :=
    isPathConnected_region_cap_cycle P
      (fun i => isPathConnected_leftRegion P hsimple i hεregpos)
      (fun i => isPathConnected_capB P hsimple i hcapRpos)
      (fun i => leftRegion_meet_capB P hsimple i hεregpos hcapRpos hcapRfs)
      (fun i => capB_meet_leftRegion_succ P hsimple i hεregpos hcapRpos hcapRfs)
  exact winding_const_of_isPreconnected P
    (left_half_subset_compl_boundary P hsimple hcapRfs) hLpc.isConnected.isPreconnected hp hq

/-- **Step 2a — a left-collar point carries winding `1`.** At a convex lex-lowest vertex
`m` (`hlex`, strict-above neighbours `hba`/`hbc`, `0 < cornerCross P m`), the witness
construction of `exists_winding_eq_one_of_cornerCross` is *localized*: at a generic low-band
height `y` the crossing of the down-edge `m−1` is the strict left-most spanning threshold, so a
point `q = (edgeThr y (m−1) + δ, y)` just to its `+x` (inside) side has `winding q = 1` (same
threshold bookkeeping) and lies in `leftRegion (m−1) εreg` (`mem_leftRegion_of_nearFoot`, foot
the crossing point, clearance from `capHeight_pos`). This anchors the interior value `1` on the
inside half-tube. -/
lemma exists_leftRegion_winding_one (hS : P.IsSimple) {εreg : ℝ} (hεregpos : 0 < εreg)
    (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2)
    (hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2)
    (hcc : 0 < cornerCross P m) :
    ∃ p, p ∈ P.leftRegion (m - 1) εreg ∧ P.winding p = 1 := by
  classical
  set ym := (toReal (P.vert m)).2 with hym
  set D := ∑ j, |(toReal (P.vert (j+1))).1 - (toReal (P.vert j)).1| with hD
  have hDpos : (0:ℝ) < D + 1 := by
    have : (0:ℝ) ≤ D := Finset.sum_nonneg (fun j _ => abs_nonneg _); linarith
  obtain ⟨y, hlo, hhiaux, hgen⟩ := exists_generic_height_mem_Ioo P ym (ym + min 1 (1/(2*(D+1))))
    (by have : (0:ℝ) < min 1 (1/(2*(D+1))) := lt_min one_pos (by positivity); linarith)
  have hhi : y < ym + 1 := lt_of_lt_of_le hhiaux (by simp)
  have hDnn : (0:ℝ) ≤ D := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hsmall : D * (y - ym) < 1/2 := by
    have hyb : y - ym < 1/(2*(D+1)) :=
      lt_of_lt_of_le (by linarith) (by
        have : ym + min 1 (1/(2*(D+1))) ≤ ym + 1/(2*(D+1)) := by
          have := min_le_right (1:ℝ) (1/(2*(D+1))); linarith
        linarith [lt_of_lt_of_le hhiaux this])
    have hkey : D * (1/(2*(D+1))) < 1/2 := by
      rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc D * (y - ym) ≤ D * (1/(2*(D+1))) :=
            mul_le_mul_of_nonneg_left (le_of_lt hyb) hDnn
      _ < 1/2 := hkey
  have hgen' : ∀ i, (toReal (P.vert i)).2 ≠ y := hgen
  have hsep := lowest_band_thresholds_separate P hS m hlex hba hbc y hlo hhi hsmall
  obtain ⟨⟨hm1lt, hm0lt⟩, hother⟩ := hsep
  have hord : P.edgeThr y (m-1) < P.edgeThr y m :=
    (cornerCross_pos_iff_threshold_order P m y hba hbc hlo).mp hcc
  have hm1S : (m - 1) ∈ P.spanningSet y := by
    rw [spanning_at_lowest_band P m hlex y hlo hhi]
    exact Or.inr ⟨by rw [sub_add_cancel], ne_of_gt hba⟩
  have hmS : m ∈ P.spanningSet y := by
    rw [spanning_at_lowest_band P m hlex y hlo hhi]
    exact Or.inl ⟨rfl, ne_of_gt hbc⟩
  have hsign : P.edgeSign y (m - 1) = -1 := by
    unfold LatticePolygon.edgeSign; rw [sub_add_cancel, if_neg (not_lt.mpr (le_of_lt hlo))]
  have hmin : ∀ i ∈ P.spanningSet y, i ≠ m - 1 → P.edgeThr y (m - 1) < P.edgeThr y i := by
    intro i hiS hine
    by_cases him : i = m
    · rw [him]; exact hord
    · exact lt_trans hm1lt (hother i hiS hine him)
  have hmne : m ≠ m - 1 := by
    intro h; rw [← h] at hba; exact lt_irrefl _ hba
  set Sother := (P.spanningSet y).erase (m - 1) with hSother
  have hSother_ne : Sother.Nonempty := ⟨m, Finset.mem_erase.mpr ⟨hmne, hmS⟩⟩
  obtain ⟨c, hcS, hcmin⟩ := Sother.exists_min_image (P.edgeThr y) hSother_ne
  have hcmem : c ∈ P.spanningSet y := (Finset.mem_erase.mp hcS).2
  have hcne : c ≠ m - 1 := (Finset.mem_erase.mp hcS).1
  have hclt : P.edgeThr y (m - 1) < P.edgeThr y c := hmin c hcmem hcne
  -- the down-edge `m−1` actually spans, so `y` is strictly below the height of `vert (m−1)`
  have hyA : y < (toReal (P.vert (m - 1))).2 := by
    have hne1 : (toReal (P.vert (m - 1))).2 ≠ (toReal (P.vert m)).2 := by
      have h0 : (toReal (P.vert (m - 1))).2 ≠ ym := ne_of_gt hba
      rwa [hym] at h0
    have hgap := lex_lowest_height_gap P m (m - 1) hlex hne1
    rw [← hym] at hgap
    linarith [hhi]
  have hAym : (0:ℝ) < (toReal (P.vert (m - 1))).2 - ym := by linarith [hba]
  have hAy : (0:ℝ) < (toReal (P.vert (m - 1))).2 - y := by linarith [hyA]
  have hvm : (m - 1) + 1 = m := sub_add_cancel m 1
  have hd1 : (toReal (P.vert (m - 1))).2 - ym ≠ 0 := ne_of_gt hAym
  have hd2 : ym - (toReal (P.vert (m - 1))).2 ≠ 0 := by intro h; apply hd1; linarith
  set s := ((toReal (P.vert (m - 1))).2 - y) / ((toReal (P.vert (m - 1))).2 - ym) with hsdef
  have hs0 : 0 < s := div_pos hAy hAym
  have hs1 : s < 1 := by rw [hsdef, div_lt_one hAym]; linarith [hlo]
  have hs : s ∈ Set.Ioo (0:ℝ) 1 := ⟨hs0, hs1⟩
  -- the foot at `s` is exactly the crossing point of edge `m−1` at height `y`
  have hsfoot : P.foot (m - 1) s = (P.edgeThr y (m - 1), y) := by
    apply Prod.ext
    · show (P.foot (m - 1) s).1 = P.edgeThr y (m - 1)
      unfold LatticePolygon.foot LatticePolygon.edgeThr crossThreshold
      rw [hvm]
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, ← hym]
      rw [hsdef]
      field_simp
      ring
    · show (P.foot (m - 1) s).2 = y
      unfold LatticePolygon.foot
      rw [hvm]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, ← hym]
      rw [hsdef]
      field_simp
      ring
  set cap := P.capHeight (m - 1) εreg s with hcapdef
  have hcappos : 0 < cap := capHeight_pos P hS (m - 1) hεregpos hs
  have hcapeps : cap ≤ εreg := capHeight_le_self P (m - 1) εreg s
  set g := P.edgeThr y c - P.edgeThr y (m - 1) with hgdef
  have hgpos : 0 < g := by rw [hgdef]; linarith [hclt]
  set δ' := min (cap / 4) (g / 2) with hδdef
  have hδpos : 0 < δ' := lt_min (by linarith) (by linarith)
  have hδcap : δ' ≤ cap / 4 := min_le_left _ _
  have hδg : δ' ≤ g / 2 := min_le_right _ _
  set q : ℝ × ℝ := (P.edgeThr y (m - 1) + δ', y) with hqdef
  -- winding `q = 1`
  have hxL : P.edgeThr y (m - 1) < P.edgeThr y (m - 1) + δ' := by linarith
  have hxR : ∀ i ∈ P.spanningSet y, i ≠ m - 1 → P.edgeThr y (m - 1) + δ' < P.edgeThr y i := by
    intro i hiS hine
    have hci : P.edgeThr y c ≤ P.edgeThr y i := hcmin i (Finset.mem_erase.mpr ⟨hine, hiS⟩)
    have hc_eq : P.edgeThr y c = P.edgeThr y (m - 1) + g := by rw [hgdef]; ring
    have hδltg : δ' < g := by linarith
    linarith
  have hwind : P.winding q = 1 := by
    rw [hqdef, winding_eq_sum_spanning P (P.edgeThr y (m - 1) + δ') y hgen']
    have hset : (P.spanningSet y).filter (fun i => P.edgeThr y (m - 1) + δ' < P.edgeThr y i)
        = (P.spanningSet y).erase (m - 1) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hiS, hlt⟩
        exact ⟨by rintro rfl; exact absurd hxL (not_lt.mpr (le_of_lt hlt)), hiS⟩
      · rintro ⟨hne, hiS⟩; exact ⟨hiS, hxR i hiS hne⟩
    rw [hset, Finset.sum_erase_eq_sub hm1S, sum_edgeSign_spanning_eq_zero P y hgen', hsign]
    ring
  -- `q ∈ leftRegion (m−1) εreg`
  have hmem : q ∈ P.leftRegion (m - 1) εreg := by
    refine mem_leftRegion_of_nearFoot P hS (m - 1) hs (δ := δ') hδpos ?_ ?_ ?_ ?_
    · rw [hsfoot, hqdef, Prod.dist_eq]
      simp only [Real.dist_eq]
      rw [show P.edgeThr y (m - 1) + δ' - P.edgeThr y (m - 1) = δ' by ring, sub_self, abs_zero,
        abs_of_nonneg hδpos.le, max_eq_left hδpos.le]
    · -- cross positivity: `q` is on the `+x` (left/inside) side of the down-edge `m−1`
      have hqf : q - P.foot (m - 1) s = ((δ' : ℝ), (0:ℝ)) := by
        rw [hsfoot, hqdef]; apply Prod.ext <;> simp
      have hfv : P.foot (m - 1) s - toReal (P.vert (m - 1)) = s • P.edgeDir (m - 1) := by
        rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
      have hsplit : q - toReal (P.vert (m - 1)) = ((δ' : ℝ), (0:ℝ)) + s • P.edgeDir (m - 1) := by
        rw [← hqf, ← hfv]; abel
      rw [hsplit]
      have hcr : cross (P.edgeDir (m - 1)) (((δ' : ℝ), (0:ℝ)) + s • P.edgeDir (m - 1))
          = - (P.edgeDir (m - 1)).2 * δ' := by
        simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [hcr]
      have hedge2 : (P.edgeDir (m - 1)).2 = (toReal (P.vert m)).2 - (toReal (P.vert (m - 1))).2 := by
        rw [LatticePolygon.edgeDir]; simp only [Prod.snd_sub, sub_add_cancel]
      rw [hedge2]
      nlinarith [mul_pos hAym hδpos]
    · -- `√2·δ < εreg`
      have hsqrt2lt : Real.sqrt 2 < 2 := by
        rw [show (2:ℝ) = Real.sqrt 4 from by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h1 : Real.sqrt 2 * δ' ≤ 2 * δ' := mul_le_mul_of_nonneg_right hsqrt2lt.le hδpos.le
      linarith [hδcap, hcapeps, hεregpos]
    · -- clearance: `3·δ < infDist (foot, edgeSeg j)` for every other edge `j`
      intro j hji
      have hle : cap ≤ Metric.infDist (P.foot (m - 1) s) (P.edgeSeg j) :=
        capHeight_le_edge P (m - 1) εreg s hji
      linarith [hδcap, hcappos, hle]
  exact ⟨q, hmem, hwind⟩

/-- **General `w_L = 1` anchor (flat-bottom safe, no convex vertex needed).** For ANY
simple, positively-oriented polygon, there is a left-collar point carrying winding `1`.
This is the standard point-in-polygon ray test (Erickson/Shimrat): at a generic height
`y` in the lowest unit band the spanning set is nonempty (some neighbour of the lex-lowest
vertex is strictly above), and the **leftmost** crossing `iL` is a down-edge whose
immediate `+x` neighbourhood point `q` has `winding q = -edgeSign y iL` (threshold
bookkeeping). Since `winding_zero_or_one` pins `winding q ∈ {0,1}` while `edgeSign` is
`±1`, the sign is forced: `edgeSign y iL = -1` and `winding q = 1`. The point `q` lies in
`leftRegion iL εreg` (`mem_leftRegion_of_nearFoot`, foot = the crossing). Works for flat
bottoms (ties at the minimum height): the leftmost low crossing sits on a left side-edge
regardless of horizontal bottom edges, so no strict-convex-lowest vertex is needed. -/
lemma exists_leftRegion_winding_one_general (hS : P.IsSimple) (hO : P.PositivelyOriented)
    {εreg : ℝ} (hεregpos : 0 < εreg) :
    ∃ (i : ZMod P.n) (p : ℝ × ℝ), p ∈ P.leftRegion i εreg ∧ P.winding p = 1 := by
  classical
  obtain ⟨m, hlex⟩ := exists_lex_lowest_vertex P
  obtain ⟨y, hlo, hhi, hgen⟩ :=
    exists_generic_height_mem_Ioo P (toReal (P.vert m)).2 ((toReal (P.vert m)).2 + 1) (by linarith)
  -- spanningSet y is nonempty: a strictly-higher neighbour of the lowest vertex spans
  have hspne : (P.spanningSet y).Nonempty := by
    by_cases hL : (toReal (P.vert (m - 1))).2 = (toReal (P.vert m)).2
    · by_cases hR : (toReal (P.vert (m + 1))).2 = (toReal (P.vert m)).2
      · exfalso
        have hcross0 : cross (toReal (P.vert (m - 1)) - toReal (P.vert m))
            (toReal (P.vert (m + 1)) - toReal (P.vert m)) = 0 := by
          unfold cross; simp only [Prod.fst_sub, Prod.snd_sub]; rw [hL, hR]; ring
        exact cornerCross_ne_zero_lex_lowest P hS m hlex
          (by rw [cornerCross_eq_neg_cross_neighbors P m, hcross0]; ring)
      · exact ⟨m, by rw [spanning_at_lowest_band P m hlex y hlo hhi]; exact Or.inl ⟨rfl, hR⟩⟩
    · exact ⟨m - 1, by
        rw [spanning_at_lowest_band P m hlex y hlo hhi]
        exact Or.inr ⟨by rw [sub_add_cancel], hL⟩⟩
  -- leftmost spanning edge `iL`
  obtain ⟨iL, hiLS, hiLmin⟩ := (P.spanningSet y).exists_min_image (P.edgeThr y) hspne
  -- the spanning set has another element `c` (even cardinality)
  have herase_ne : ((P.spanningSet y).erase iL).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.erase_eq_empty_iff] at h
    have hsum := sum_edgeSign_spanning_eq_zero P y hgen
    rcases h with h | h
    · rw [h] at hiLS; exact absurd hiLS (Finset.notMem_empty iL)
    · rw [h, Finset.sum_singleton] at hsum
      rcases edgeSign_eq_one_or_neg_one P y iL with he | he <;> rw [he] at hsum <;> norm_num at hsum
  obtain ⟨c, hcE, hcmin⟩ := ((P.spanningSet y).erase iL).exists_min_image (P.edgeThr y) herase_ne
  have hcS : c ∈ P.spanningSet y := (Finset.mem_erase.mp hcE).2
  have hcne : c ≠ iL := (Finset.mem_erase.mp hcE).1
  -- raw spanning conditions for distinctness of thresholds
  have hiLraw : ((toReal (P.vert iL)).2 < y ∧ y < (toReal (P.vert (iL + 1))).2) ∨
      ((toReal (P.vert (iL + 1))).2 < y ∧ y < (toReal (P.vert iL)).2) := by
    have h := hiLS; simp only [spanningSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hcraw : ((toReal (P.vert c)).2 < y ∧ y < (toReal (P.vert (c + 1))).2) ∨
      ((toReal (P.vert (c + 1))).2 < y ∧ y < (toReal (P.vert c)).2) := by
    have h := hcS; simp only [spanningSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  -- `iL` crosses strictly left of `c` (distinct thresholds under simplicity)
  have hiLc : P.edgeThr y iL < P.edgeThr y c := by
    refine lt_of_le_of_ne (hiLmin c hcS) ?_
    unfold LatticePolygon.edgeThr
    exact crossThreshold_ne_distinct_spanning P hS y hgen iL c (Ne.symm hcne) hiLraw hcraw
  -- winding just to the `+x` side of the leftmost crossing equals `-edgeSign y iL`
  have hwformula : ∀ δ : ℝ, 0 < δ → δ < P.edgeThr y c - P.edgeThr y iL →
      P.winding (P.edgeThr y iL + δ, y) = - P.edgeSign y iL := by
    intro δ hδ hδg
    rw [winding_eq_sum_spanning P (P.edgeThr y iL + δ) y hgen]
    have hset : (P.spanningSet y).filter (fun i => P.edgeThr y iL + δ < P.edgeThr y i)
        = (P.spanningSet y).erase iL := by
      ext i; simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hiS, hlt⟩; exact ⟨by rintro rfl; linarith, hiS⟩
      · rintro ⟨hine, hiS⟩
        have hci : P.edgeThr y c ≤ P.edgeThr y i := hcmin i (Finset.mem_erase.mpr ⟨hine, hiS⟩)
        exact ⟨hiS, by linarith⟩
    rw [hset, Finset.sum_erase_eq_sub hiLS, sum_edgeSign_spanning_eq_zero P y hgen]; ring
  -- such points lie off the boundary
  have hoffb : ∀ δ : ℝ, 0 < δ → δ < P.edgeThr y c - P.edgeThr y iL →
      (P.edgeThr y iL + δ, y) ∉ P.boundary := by
    intro δ hδ hδg
    refine notMem_boundary_of_between_thresholds P y hgen _ (P.edgeThr y iL) (P.edgeThr y c)
      ⟨by linarith, by linarith⟩ ?_
    intro i hiS
    by_cases hii : i = iL
    · subst hii; exact Or.inl le_rfl
    · exact Or.inr (hcmin i (Finset.mem_erase.mpr ⟨hii, hiS⟩))
  -- the leftmost crossing is a down-edge: `winding ∈ {0,1} ∩ {±1} = {1}` forces the sign
  have hsign : P.edgeSign y iL = -1 := by
    have hδ0 : (0:ℝ) < (P.edgeThr y c - P.edgeThr y iL) / 2 := by linarith
    have hδ0g : (P.edgeThr y c - P.edgeThr y iL) / 2 < P.edgeThr y c - P.edgeThr y iL := by linarith
    have hw := hwformula _ hδ0 hδ0g
    rcases winding_zero_or_one P hS hO _ (hoffb _ hδ0 hδ0g) with h0 | h1
    · rw [h0] at hw
      rcases edgeSign_eq_one_or_neg_one P y iL with he | he <;> rw [he] at hw <;> norm_num at hw
    · have heq : - P.edgeSign y iL = 1 := by rw [← hw, h1]
      omega
  -- decode the down-edge geometry
  have hbelow : (toReal (P.vert (iL + 1))).2 < y := by
    have hnlt : ¬ (y < (toReal (P.vert (iL + 1))).2) := by
      intro h; unfold LatticePolygon.edgeSign at hsign; rw [if_pos h] at hsign; norm_num at hsign
    exact lt_of_le_of_ne (not_lt.mp hnlt) (hgen (iL + 1))
  have hyA : y < (toReal (P.vert iL)).2 := by
    rcases hiLraw with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact absurd h2 (not_lt.mpr (le_of_lt hbelow))
    · exact h2
  have hAym : (0:ℝ) < (toReal (P.vert iL)).2 - (toReal (P.vert (iL + 1))).2 := by linarith
  have hnum : (0:ℝ) < (toReal (P.vert iL)).2 - y := by linarith
  set s := ((toReal (P.vert iL)).2 - y) / ((toReal (P.vert iL)).2 - (toReal (P.vert (iL + 1))).2)
    with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos hnum hAym
  have hs1 : s < 1 := by rw [hsdef, div_lt_one hAym]; linarith
  have hs : s ∈ Set.Ioo (0:ℝ) 1 := ⟨hs0, hs1⟩
  have hd1 : (toReal (P.vert iL)).2 - (toReal (P.vert (iL + 1))).2 ≠ 0 := ne_of_gt hAym
  have hd2 : (toReal (P.vert (iL + 1))).2 - (toReal (P.vert iL)).2 ≠ 0 := by
    intro h; apply hd1; linarith
  have hsfoot : P.foot iL s = (P.edgeThr y iL, y) := by
    apply Prod.ext
    · show (P.foot iL s).1 = P.edgeThr y iL
      unfold LatticePolygon.foot LatticePolygon.edgeThr crossThreshold
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [hsdef]; field_simp; ring
    · show (P.foot iL s).2 = y
      unfold LatticePolygon.foot
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hsdef]; field_simp; ring
  set cap := P.capHeight iL εreg s with hcapdef
  have hcappos : 0 < cap := capHeight_pos P hS iL hεregpos hs
  have hcapeps : cap ≤ εreg := capHeight_le_self P iL εreg s
  set g := P.edgeThr y c - P.edgeThr y iL with hgdef
  have hgpos : 0 < g := by rw [hgdef]; linarith
  set δ' := min (cap / 4) (g / 2) with hδdef
  have hδpos : 0 < δ' := lt_min (by linarith) (by linarith)
  have hδcap : δ' ≤ cap / 4 := min_le_left _ _
  have hδg : δ' ≤ g / 2 := min_le_right _ _
  have hδltg : δ' < g := by linarith
  set q : ℝ × ℝ := (P.edgeThr y iL + δ', y) with hqdef
  have hwind : P.winding q = 1 := by
    rw [hqdef, hwformula δ' hδpos hδltg, hsign]; norm_num
  have hmem : q ∈ P.leftRegion iL εreg := by
    refine mem_leftRegion_of_nearFoot P hS iL hs (δ := δ') hδpos ?_ ?_ ?_ ?_
    · rw [hsfoot, hqdef, Prod.dist_eq]
      simp only [Real.dist_eq]
      rw [show P.edgeThr y iL + δ' - P.edgeThr y iL = δ' by ring, sub_self, abs_zero,
        abs_of_nonneg hδpos.le, max_eq_left hδpos.le]
    · have hqf : q - P.foot iL s = ((δ' : ℝ), (0:ℝ)) := by
        rw [hsfoot, hqdef]; apply Prod.ext <;> simp
      have hfv : P.foot iL s - toReal (P.vert iL) = s • P.edgeDir iL := by
        rw [LatticePolygon.foot, LatticePolygon.edgeDir]; module
      have hsplit : q - toReal (P.vert iL) = ((δ' : ℝ), (0:ℝ)) + s • P.edgeDir iL := by
        rw [← hqf, ← hfv]; abel
      rw [hsplit]
      have hcr : cross (P.edgeDir iL) (((δ' : ℝ), (0:ℝ)) + s • P.edgeDir iL)
          = - (P.edgeDir iL).2 * δ' := by
        simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [hcr]
      have hedge2 : (P.edgeDir iL).2 = (toReal (P.vert (iL + 1))).2 - (toReal (P.vert iL)).2 := by
        rw [LatticePolygon.edgeDir]; simp only [Prod.snd_sub]
      rw [hedge2]; nlinarith [mul_pos hAym hδpos]
    · have hsqrt2lt : Real.sqrt 2 < 2 := by
        rw [show (2:ℝ) = Real.sqrt 4 from by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h1 : Real.sqrt 2 * δ' ≤ 2 * δ' := mul_le_mul_of_nonneg_right hsqrt2lt.le hδpos.le
      linarith [hδcap, hcapeps, hεregpos]
    · intro j hji
      have hle : cap ≤ Metric.infDist (P.foot iL s) (P.edgeSeg j) :=
        capHeight_le_edge P iL εreg s hji
      linarith [hδcap, hcappos, hle]
  exact ⟨iL, q, hmem, hwind⟩

/-- **Step 2 — the inside half-tube `L` carries winding `1`.** Combining the left-collar
witness `exists_leftRegion_winding_one` (a point of `leftRegion (m−1) εreg ⊆ L` with
`winding = 1`) with the constancy of `winding` on `L` (`winding_const_on_leftTube`) pins the
*single* value of `winding` on the whole inside half-tube to `1`. Needs only a convex
lex-lowest vertex `m` (no orientation of any clip). -/
lemma leftTube_winding_eq_one (hS : P.IsSimple) {εreg capR : ℝ}
    (hεregpos : 0 < εreg) (hcapRpos : 0 < capR) (hcapRfs : capR ≤ P.featureSize)
    (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2)
    (hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2)
    (hcc : 0 < cornerCross P m) {q : ℝ × ℝ}
    (hq : q ∈ (⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR)) :
    P.winding q = 1 := by
  obtain ⟨p, hpmem, hpw⟩ := exists_leftRegion_winding_one P hS hεregpos m hlex hba hbc hcc
  have hpL : p ∈ (⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i capR) :=
    Or.inl (Set.mem_iUnion.mpr ⟨m - 1, hpmem⟩)
  rw [winding_const_on_leftTube P hS hεregpos hcapRpos hcapRfs hq hpL, hpw]

/-- **Any inside-collar point carries winding `1`.** Packaging
`exists_leftRegion_winding_one_general` (a witness leftRegion point of winding `1`) with
`winding_const_on_leftTube` (winding is constant on the whole inside half-tube
`(⋃ leftRegion) ∪ (⋃ capB)`): every point of *any* `leftRegion k εreg` has `P.winding = 1`,
with the lex-lowest-vertex anchor discharged internally. The convenience form of
`leftTube_winding_eq_one` for a positively-oriented simple polygon. -/
lemma leftRegion_winding_one (hS : P.IsSimple) (hO : P.PositivelyOriented)
    {εreg : ℝ} (hεregpos : 0 < εreg) (k : ZMod P.n) {q : ℝ × ℝ}
    (hq : q ∈ P.leftRegion k εreg) : P.winding q = 1 := by
  obtain ⟨i, p, hp, hpw⟩ := exists_leftRegion_winding_one_general P hS hO hεregpos
  have hqU : q ∈ (⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i P.featureSize) :=
    Or.inl (Set.mem_iUnion.mpr ⟨k, hq⟩)
  have hpU : p ∈ (⋃ i, P.leftRegion i εreg) ∪ (⋃ i, P.capB i P.featureSize) :=
    Or.inl (Set.mem_iUnion.mpr ⟨i, hp⟩)
  rw [← hpw]
  exact (winding_const_on_leftTube P hS hεregpos (featureSize_pos P hS) (le_refl _) hpU hqU).symm

/-- **Step 3 — the open ear meets the inside half-tube.** A point just inside the ear leg
`edgeSeg m` carries simultaneous membership: pushing the midpoint `mid` of edge `m` a tiny
amount `ε` toward the ear-triangle centroid `cen` keeps all three open-ear half-plane
functionals strictly positive (their values are positive convex combinations of the
`mid`/`cen` values, the latter all `> 0` by `cornerCross`/`earTri_cross_base_pos`), while the
displaced point stays at distance `< εreg`-collar from the foot `mid = foot m ½`, with the
left-turn `cross > 0` (the first open-ear functional itself), so `mem_leftRegion_of_nearFoot`
places it in `leftRegion m εreg`. Hence `openEar R m ∩ leftRegion m εreg ≠ ∅`: the shared
point linking the open-ear value to the inside-tube value `1`. -/
lemma exists_openEar_mem_leftRegion (hS : P.IsSimple) {εreg : ℝ} (hεregpos : 0 < εreg)
    (m : ℕ) (hm : P.n = m + 2) (_ : 2 ≤ m)
    (hear : isEarVertex P ((m : ZMod P.n) + 1)) :
    ∃ p, p ∈ openEar P m ∧ p ∈ P.leftRegion (m : ZMod P.n) εreg := by
  classical
  set a := toReal (P.vert (m : ZMod P.n)) with ha
  set b := toReal (P.vert ((m : ZMod P.n) + 1)) with hb
  set c := toReal (P.vert (0 : ZMod P.n)) with hc
  have hmp1mp1 : ((m : ZMod P.n) + 1) + 1 = (0 : ZMod P.n) := by
    have hz : ((m + 2 : ℕ) : ZMod P.n) = 0 := by rw [← hm]; exact ZMod.natCast_self P.n
    push_cast at hz; linear_combination hz
  have hCC : 0 < cross (b - a) (c - b) := by
    have h := hear.1
    unfold cornerCross at h
    rwa [show ((m : ZMod P.n) + 1 - 1) = (m : ZMod P.n) by ring, hmp1mp1] at h
  have hBASE : 0 < cross (b - a) (c - a) := earTri_cross_base_pos P m hm hear
  set mid : ℝ × ℝ := ((a.1 + b.1) / 2, (a.2 + b.2) / 2) with hmiddef
  set cen : ℝ × ℝ := ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3) with hcendef
  have hmidfoot : P.foot (m : ZMod P.n) (1 / 2) = mid := by
    rw [LatticePolygon.foot, hmiddef, ← ha, ← hb]
    apply Prod.ext <;>
      · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hg1mid : cross (b - a) (mid - a) = 0 := by
    rw [hmiddef]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hg1cen : cross (b - a) (cen - a) = (1 / 3) * cross (b - a) (c - b) := by
    rw [hcendef]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hg2mid : cross (c - b) (mid - b) = (1 / 2) * cross (b - a) (c - b) := by
    rw [hmiddef]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hg2cen : cross (c - b) (cen - b) = (1 / 3) * cross (b - a) (c - b) := by
    rw [hcendef]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hg3mid : cross (a - c) (mid - c) = (1 / 2) * cross (b - a) (c - a) := by
    rw [hmiddef]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hg3cen : cross (a - c) (cen - c) = (1 / 3) * cross (b - a) (c - b) := by
    rw [hcendef]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hdcm : 0 < dist cen mid := by
    rw [dist_pos]; intro h
    have hcontra : cross (b - a) (cen - a) = cross (b - a) (mid - a) := by rw [h]
    rw [hg1cen, hg1mid] at hcontra; nlinarith [hCC]
  set cap := P.capHeight (m : ZMod P.n) εreg (1 / 2) with hcapdef
  have hs12 : (1 / 2 : ℝ) ∈ Set.Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hcappos : 0 < cap := capHeight_pos P hS (m : ZMod P.n) hεregpos hs12
  have hcapeps : cap ≤ εreg := capHeight_le_self P (m : ZMod P.n) εreg (1 / 2)
  set ε := min (1 / 2) (cap / (4 * dist cen mid)) with hεdef
  have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεlt1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set δ := ε * dist cen mid with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact mul_pos hεpos hdcm
  have hδle : δ ≤ cap / 4 := by
    have hεle : ε ≤ cap / (4 * dist cen mid) := min_le_right _ _
    rw [hδdef]
    calc ε * dist cen mid ≤ (cap / (4 * dist cen mid)) * dist cen mid :=
          mul_le_mul_of_nonneg_right hεle hdcm.le
      _ = cap / 4 := by field_simp
  set q3 : ℝ × ℝ := (1 - ε) • mid + ε • cen with hq3def
  -- the three open-ear functionals at `q3` are positive convex combinations
  have hq3_1 : cross (b - a) (q3 - a) = (1 - ε) * cross (b - a) (mid - a)
      + ε * cross (b - a) (cen - a) := by rw [hq3def]; exact cross_affine_seg_pk (b - a) a mid cen ε
  have hq3_2 : cross (c - b) (q3 - b) = (1 - ε) * cross (c - b) (mid - b)
      + ε * cross (c - b) (cen - b) := by rw [hq3def]; exact cross_affine_seg_pk (c - b) b mid cen ε
  have hq3_3 : cross (a - c) (q3 - c) = (1 - ε) * cross (a - c) (mid - c)
      + ε * cross (a - c) (cen - c) := by rw [hq3def]; exact cross_affine_seg_pk (a - c) c mid cen ε
  have hpos1 : 0 < cross (b - a) (q3 - a) := by
    rw [hq3_1, hg1mid, hg1cen]; nlinarith [hCC, hεpos]
  have hpos2 : 0 < cross (c - b) (q3 - b) := by
    rw [hq3_2, hg2mid, hg2cen]; nlinarith [hCC, hεpos, hεlt1]
  have hpos3 : 0 < cross (a - c) (q3 - c) := by
    rw [hq3_3, hg3mid, hg3cen]; nlinarith [hCC, hBASE, hεpos, hεlt1]
  refine ⟨q3, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← ha, ← hb]; exact hpos1
  · rw [← hb, ← hc]; exact hpos2
  · rw [← ha, ← hc]; exact hpos3
  · -- `q3 ∈ leftRegion m εreg`
    refine mem_leftRegion_of_nearFoot P hS (m : ZMod P.n) hs12 (δ := δ) hδpos ?_ ?_ ?_ ?_
    · -- `dist q3 (foot m ½) = δ`
      rw [hmidfoot, dist_eq_norm,
        show q3 - mid = ε • (cen - mid) from by rw [hq3def]; module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hεpos.le, ← dist_eq_norm, hδdef]
    · -- left-turn `cross > 0` (the first open-ear functional)
      have hed : P.edgeDir (m : ZMod P.n) = b - a := by
        rw [LatticePolygon.edgeDir, ← ha, ← hb]
      rw [hed, ← ha]; exact hpos1
    · -- `√2·δ < εreg`
      have hsqrt2lt : Real.sqrt 2 < 2 := by
        rw [show (2:ℝ) = Real.sqrt 4 from by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h1 : Real.sqrt 2 * δ ≤ 2 * δ := mul_le_mul_of_nonneg_right hsqrt2lt.le hδpos.le
      linarith [hδle, hcapeps, hεregpos]
    · -- clearance
      intro j hji
      have hle : cap ≤ Metric.infDist (P.foot (m : ZMod P.n) (1 / 2)) (P.edgeSeg j) :=
        capHeight_le_edge P (m : ZMod P.n) εreg (1 / 2) hji
      linarith [hδle, hcappos, hle]

/-- **Winding is `1` on the whole open ear (FULLY UNCONDITIONAL).** For any simple,
positively-oriented `R`, winding is `1` on `openEar R m`. No unique-lowest / strict-convex
hypothesis: the inside half-tube `L` carries the single value `1` via the general
point-in-polygon anchor `exists_leftRegion_winding_one_general` (leftmost low crossing,
sign forced by `winding_zero_or_one`), which handles flat bottoms (ties at the minimum
height) directly. The open ear meets `L` in a shared point (`exists_openEar_mem_leftRegion`),
and `winding` is constant on the connected open ear (`winding_const_on_openEar`). -/
lemma winding_one_on_open_ear (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    ∀ q ∈ openEar R m, R.winding q = 1 := by
  obtain ⟨p, hpO, hpL⟩ := exists_openEar_mem_leftRegion R hS (εreg := 1) one_pos m hm hm2 hear
  obtain ⟨i, w, hwmem, hww⟩ := exists_leftRegion_winding_one_general R hS hO (εreg := 1) one_pos
  have hpw : R.winding p = 1 := by
    rw [winding_const_on_leftTube R hS one_pos (featureSize_pos R hS) (le_refl _)
      (Or.inl (Set.mem_iUnion.mpr ⟨(m : ZMod R.n), hpL⟩))
      (Or.inl (Set.mem_iUnion.mpr ⟨i, hwmem⟩))]
    exact hww
  intro q hq
  rw [winding_const_on_openEar R hS m hm hm2 hear hq hpO]; exact hpw

/-! ### Conjunct 2 (clip orientation), area-inclusion route

The clip `deleteLast R` of an empty ear is positively oriented.  Route:
`deleteLast.shoelace = R.shoelace − earTri.shoelace`; we show `earTri.shoelace ≤
R.shoelace` by area inclusion (`{earTri.winding = 1} ⊆ {R.winding = 1}` up to the
null ear-triangle boundary), giving `0 ≤ deleteLast.shoelace`. -/

/-- The closed half-plane `{p | 0 ≤ cross u (p − w)}` is convex (it is `{cross u w ≤
cross u ·}`, a closed half-space of the linear functional `cross u`). -/
lemma convex_nonneg_cross (u w : ℝ × ℝ) :
    Convex ℝ {p : ℝ × ℝ | 0 ≤ cross u (p - w)} := by
  have hset : {p : ℝ × ℝ | 0 ≤ cross u (p - w)} = {p : ℝ × ℝ | cross u w ≤ cross u p} := by
    ext p; simp only [Set.mem_setOf_eq, cross, Prod.fst_sub, Prod.snd_sub]
    constructor <;> intro h <;> nlinarith
  rw [hset]; exact convex_halfSpace_ge (isLinearMap_cross u) (cross u w)

/-- **Winding `0` strictly off a half-plane that contains the whole boundary.** If the
boundary of a polygon `T` lies in the closed half-plane `{0 ≤ cross u (· − w)}` and `q`
is strictly on the other side (`cross u (q − w) < 0`), then `T.winding q = 0`: the ray
`q + t·(u₂, −u₁)` (`t ≥ 0`) stays strictly on the negative side (hence off the
boundary), is preconnected, and reaches arbitrarily far out where winding vanishes. -/
lemma winding_zero_of_neg_halfplane (T : LatticePolygon) (w u q : ℝ × ℝ)
    (hu : u ≠ 0)
    (hbd : T.boundary ⊆ {p : ℝ × ℝ | 0 ≤ cross u (p - w)})
    (hq : cross u (q - w) < 0) :
    T.winding q = 0 := by
  classical
  set dir : ℝ × ℝ := (u.2, -u.1) with hdir
  have hcu : cross u dir = -(u.1 ^ 2 + u.2 ^ 2) := by simp only [hdir, cross]; ring
  have hunorm : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    rcases eq_or_ne u.1 0 with h1 | h1
    · rcases eq_or_ne u.2 0 with h2 | h2
      · exact absurd (Prod.ext h1 h2) hu
      · have : 0 < u.2 ^ 2 := (sq_nonneg u.2).lt_of_ne (Ne.symm (pow_ne_zero 2 h2))
        nlinarith [sq_nonneg u.1]
    · have : 0 < u.1 ^ 2 := (sq_nonneg u.1).lt_of_ne (Ne.symm (pow_ne_zero 2 h1))
      nlinarith [sq_nonneg u.2]
  have hcross_t : ∀ t : ℝ, cross u ((q + t • dir) - w) = cross u (q - w) + t * cross u dir := by
    intro t
    simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  have hray_off : ∀ t : ℝ, 0 ≤ t → (q + t • dir) ∉ T.boundary := by
    intro t ht hmem
    have hge := hbd hmem
    rw [Set.mem_setOf_eq, hcross_t, hcu] at hge
    nlinarith [mul_nonneg ht hunorm.le]
  set s : Set (ℝ × ℝ) := (fun t : ℝ => q + t • dir) '' Set.Ici 0 with hsdef
  have hcont : Continuous (fun t : ℝ => q + t • dir) := by fun_prop
  have hspre : IsPreconnected s := isPreconnected_Ici.image _ hcont.continuousOn
  have hssub : s ⊆ T.boundaryᶜ := by rintro _ ⟨t, ht, rfl⟩; exact hray_off t ht
  have hqs : q ∈ s := ⟨0, Set.self_mem_Ici, by simp⟩
  obtain ⟨Rc, hRc⟩ := winding_zero_on_cobounded T
  have hdirne : dir ≠ 0 := by
    intro h
    rw [hdir, Prod.mk_eq_zero] at h
    exact hu (Prod.ext (neg_eq_zero.mp h.2) h.1)
  have hdirpos : 0 < ‖dir‖ := norm_pos_iff.mpr hdirne
  set t₀ : ℝ := (|Rc| + ‖q‖ + 1) / ‖dir‖ with ht₀
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  set q₀ : ℝ × ℝ := q + t₀ • dir with hq₀
  have hq₀s : q₀ ∈ s := ⟨t₀, Set.mem_Ici.2 ht₀0, rfl⟩
  have htri : ‖t₀ • dir‖ ≤ ‖q₀‖ + ‖q‖ := by
    have he : t₀ • dir = q₀ - q := by rw [hq₀]; abel
    rw [he]; exact norm_sub_le _ _
  have hnt : ‖t₀ • dir‖ = t₀ * ‖dir‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀0]
  have ht0d : t₀ * ‖dir‖ = |Rc| + ‖q‖ + 1 := by
    rw [ht₀]; field_simp
  rw [hnt, ht0d] at htri
  have hfar : Rc < ‖q₀‖ := by nlinarith [le_abs_self Rc]
  exact winding_zero_of_joinedIn_far T ⟨s, hssub, hspre, hqs, hq₀s⟩ ⟨Rc, hRc, hfar⟩

/-- **Off the closed ear triangle, the ear-triangle winding vanishes.** A point `q`
not in the closed triangle `(vₘ, vₘ₊₁, v₀)` (some `inTriangle` half-plane strictly
fails) has `(earTri R m hm).winding q = 0`: the boundary of `earTri` lies in each of
the three closed half-planes, so `winding_zero_of_neg_halfplane` applies. -/
lemma earTri_winding_zero_of_not_inTriangle (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) (q : ℝ × ℝ)
    (hq : ¬ inTriangle (toReal (R.vert (m : ZMod R.n)))
            (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0)) q) :
    (earTri R m hm).winding q = 0 := by
  set a := toReal (R.vert (m : ZMod R.n)) with ha
  set b := toReal (R.vert ((m : ZMod R.n) + 1)) with hb
  set c := toReal (R.vert 0) with hc
  have hpos : 0 < cross (b - a) (c - a) := by
    have h2 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
      have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
      push_cast at hz; linear_combination hz
    have h1 : ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) := by ring
    have key : cross (b - a) (c - a) = cornerCross R ((m : ZMod R.n) + 1) := by
      unfold cornerCross; rw [h1, h2, ← ha, ← hb, ← hc]
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [key]; exact hear.1
  have hCCW : 0 ≤ cross (b - a) (c - a) := hpos.le
  have hu1 : b - a ≠ 0 := by intro h; rw [h] at hpos; simp [cross] at hpos
  have hu2 : c - b ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, cross_self] at hpos; exact lt_irrefl 0 hpos
  have hu3 : a - c ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hpos; simp [cross] at hpos
  have hbeq := earTri_boundary_eq R m hm
  rw [← ha, ← hb, ← hc] at hbeq
  have hva := inTriangle_fst a b c hCCW
  have hvb := inTriangle_snd a b c hCCW
  have hvc := inTriangle_thd a b c hCCW
  have hbd1 : (earTri R m hm).boundary ⊆ {p : ℝ × ℝ | 0 ≤ cross (b - a) (p - a)} := by
    rw [hbeq]
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · exact (convex_nonneg_cross (b - a) a).segment_subset hva.1 hvb.1
    · exact (convex_nonneg_cross (b - a) a).segment_subset hvb.1 hvc.1
    · exact (convex_nonneg_cross (b - a) a).segment_subset hvc.1 hva.1
  have hbd2 : (earTri R m hm).boundary ⊆ {p : ℝ × ℝ | 0 ≤ cross (c - b) (p - b)} := by
    rw [hbeq]
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · exact (convex_nonneg_cross (c - b) b).segment_subset hva.2.1 hvb.2.1
    · exact (convex_nonneg_cross (c - b) b).segment_subset hvb.2.1 hvc.2.1
    · exact (convex_nonneg_cross (c - b) b).segment_subset hvc.2.1 hva.2.1
  have hbd3 : (earTri R m hm).boundary ⊆ {p : ℝ × ℝ | 0 ≤ cross (a - c) (p - c)} := by
    rw [hbeq]
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · exact (convex_nonneg_cross (a - c) c).segment_subset hva.2.2 hvb.2.2
    · exact (convex_nonneg_cross (a - c) c).segment_subset hvb.2.2 hvc.2.2
    · exact (convex_nonneg_cross (a - c) c).segment_subset hvc.2.2 hva.2.2
  rw [inTriangle] at hq
  by_cases h1 : 0 ≤ cross (b - a) (q - a)
  · by_cases h2 : 0 ≤ cross (c - b) (q - b)
    · by_cases h3 : 0 ≤ cross (a - c) (q - c)
      · exact absurd ⟨h1, h2, h3⟩ hq
      · push Not at h3
        exact winding_zero_of_neg_halfplane (earTri R m hm) c (a - c) q hu3 hbd3 h3
    · push Not at h2
      exact winding_zero_of_neg_halfplane (earTri R m hm) b (c - b) q hu2 hbd2 h2
  · push Not at h1
    exact winding_zero_of_neg_halfplane (earTri R m hm) a (b - a) q hu1 hbd1 h1

/-- **The `earTri`-inside is contained in the `R`-inside, modulo the (null) ear-triangle
boundary.** Every point with `(earTri R m hm).winding = 1` is either inside `R`
(`R.winding = 1`, on the open ear via `winding_one_on_open_ear`) or on `earTri`'s
boundary (it is in the closed triangle by `earTri_winding_zero_of_not_inTriangle` but on
one of the three edge lines). -/
lemma earTri_winding_one_subset (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    {q : ℝ × ℝ | (earTri R m hm).winding q = 1}
      ⊆ {q : ℝ × ℝ | R.winding q = 1} ∪ (earTri R m hm).boundary := by
  set a := toReal (R.vert (m : ZMod R.n)) with ha
  set b := toReal (R.vert ((m : ZMod R.n) + 1)) with hb
  set c := toReal (R.vert 0) with hc
  have hpos : 0 < cross (b - a) (c - a) := by
    have h2 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
      have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
      push_cast at hz; linear_combination hz
    have h1 : ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) := by ring
    have key : cross (b - a) (c - a) = cornerCross R ((m : ZMod R.n) + 1) := by
      unfold cornerCross; rw [h1, h2, ← ha, ← hb, ← hc]
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [key]; exact hear.1
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  have hinTri : inTriangle a b c z := by
    by_contra hnot
    rw [ha, hb, hc] at hnot
    have hzero := earTri_winding_zero_of_not_inTriangle R m hm hear z hnot
    rw [hzero] at hz; exact absurd hz.symm one_ne_zero
  by_cases hopen : 0 < cross (b - a) (z - a) ∧ 0 < cross (c - b) (z - b)
      ∧ 0 < cross (a - c) (z - c)
  · left
    have hzopen : z ∈ openEar R m := by
      simp only [openEar, Set.mem_setOf_eq, ← ha, ← hb, ← hc]; exact hopen
    exact winding_one_on_open_ear R hS hO m hm hm2 hear z hzopen
  · right
    rw [earTri_boundary_eq R m hm, ← ha, ← hb, ← hc]
    obtain ⟨hf1, hf2, hf3⟩ := hinTri
    push Not at hopen
    by_cases e1 : cross (b - a) (z - a) = 0
    · exact Or.inl (Or.inl (mem_segment_ab_of_inTriangle_f1_zero a b c z hpos ⟨hf1, hf2, hf3⟩ e1))
    · have hf1' : 0 < cross (b - a) (z - a) := hf1.lt_of_ne (Ne.symm e1)
      by_cases e2 : cross (c - b) (z - b) = 0
      · exact Or.inl (Or.inr (mem_segment_bc_of_inTriangle_f2_zero a b c z hpos ⟨hf1, hf2, hf3⟩ e2))
      · have hf2' : 0 < cross (c - b) (z - b) := hf2.lt_of_ne (Ne.symm e2)
        have e3 : cross (a - c) (z - c) = 0 := le_antisymm (hopen hf1' hf2') hf3
        exact Or.inr (mem_segment_ca_of_inTriangle_f3_zero a b c z hpos ⟨hf1, hf2, hf3⟩ e3)

/-- **The ear triangle's signed area is dominated by `R`'s** (`earTri.shoelace ≤
R.shoelace`).  Both are areas of the respective inside regions (Green + `h01`); the
`earTri`-inside sits inside the `R`-inside up to the null ear-triangle boundary
(`earTri_winding_one_subset`), so `measure_mono` gives the inequality. -/
lemma earTri_shoelace_le (R : LatticePolygon) (hS : R.IsSimple) (hO : R.PositivelyOriented)
    (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    (earTri R m hm).shoelace ≤ R.shoelace := by
  have hearS : (earTri R m hm).IsSimple :=
    earTri_isSimple_of_cornerCross_ne R m hm (ne_of_gt hear.1)
  have hearO : (earTri R m hm).PositivelyOriented := earTri_positivelyOriented_of_isEar R m hm hear
  have hET : (earTri R m hm).shoelace
      = (MeasureTheory.volume {q : ℝ × ℝ | (earTri R m hm).winding q = 1}).toReal := by
    have harea : (earTri R m hm).area = (earTri R m hm).shoelace := by
      rw [area_eq_integral_of_mem01_ae _ (triangle_h01_ae (earTri R m hm) hearS rfl hearO),
        greens_theorem]
    rw [← harea]; rfl
  have hR : R.shoelace = (MeasureTheory.volume {q : ℝ × ℝ | R.winding q = 1}).toReal := by
    have harea : R.area = R.shoelace := by
      rw [area_eq_integral_of_mem01_ae _ (h01_ae R hS hO), greens_theorem]
    rw [← harea]; rfl
  have hsub := earTri_winding_one_subset R hS hO m hm hm2 hear
  have hbnull : MeasureTheory.volume (earTri R m hm).boundary = 0 :=
    volume_boundary_eq_zero (earTri R m hm) hearS
  have hvol : MeasureTheory.volume {q : ℝ × ℝ | (earTri R m hm).winding q = 1}
      ≤ MeasureTheory.volume {q : ℝ × ℝ | R.winding q = 1} := by
    calc MeasureTheory.volume {q : ℝ × ℝ | (earTri R m hm).winding q = 1}
        ≤ MeasureTheory.volume ({q : ℝ × ℝ | R.winding q = 1} ∪ (earTri R m hm).boundary) :=
          MeasureTheory.measure_mono hsub
      _ ≤ MeasureTheory.volume {q : ℝ × ℝ | R.winding q = 1}
            + MeasureTheory.volume (earTri R m hm).boundary := MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume {q : ℝ × ℝ | R.winding q = 1} := by rw [hbnull, add_zero]
  have hfin : MeasureTheory.volume {q : ℝ × ℝ | R.winding q = 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (windingSupport_volume_ne_top R) (MeasureTheory.measure_mono ?_)
    intro x hx; simp only [Set.mem_setOf_eq] at hx ⊢; rw [hx]; exact one_ne_zero
  rw [hET, hR]
  exact ENNReal.toReal_mono hfin hvol

/-- **Clip signed area is nonnegative** (`0 ≤ (deleteLast R).shoelace`).  Immediate from
`shoelace_eq_deleteLast_add_earTri` and `earTri_shoelace_le`. -/
lemma deleteLast_shoelace_nonneg (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    0 ≤ (deleteLast R h2).shoelace := by
  have hadd := shoelace_eq_deleteLast_add_earTri R h2 m hm
  have hle := earTri_shoelace_le R hS hO m hm hm2 hear
  linarith

/-- **Conjunct 2, reduced to clip-area nonvanishing.** With the area-inclusion bound
`0 ≤ (deleteLast R).shoelace` (`deleteLast_shoelace_nonneg`), the clip is positively
oriented as soon as its signed area is nonzero. The remaining input
`(deleteLast R h2).shoelace ≠ 0` is exactly the classical fact *a simple polygon has
nonzero signed area* (its inside has positive measure); `deleteLast R` is simple by
`deleteLast_isSimple_of_emptyEar`. -/
lemma deleteLast_positivelyOriented_of_shoelace_ne_zero (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1))
    (hne : (deleteLast R h2).shoelace ≠ 0) :
    (deleteLast R h2).PositivelyOriented :=
  lt_of_le_of_ne (deleteLast_shoelace_nonneg R hS hO h2 m hm hm2 hear) (Ne.symm hne)

/-- **Conjunct 2 — the clip of an empty ear is positively oriented.** The clip
`deleteLast R` is simple (`deleteLast_isSimple_of_emptyEar`), so it has nonzero signed
area (`shoelace_ne_zero_of_isSimple`); combined with `0 ≤ (deleteLast R).shoelace`
(`deleteLast_shoelace_nonneg`) this gives `0 < (deleteLast R).shoelace`, i.e.
`(deleteLast R).PositivelyOriented`. -/
lemma deleteLast_positivelyOriented_of_emptyEar (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    (deleteLast R h2).PositivelyOriented :=
  deleteLast_positivelyOriented_of_shoelace_ne_zero R hS hO h2 m hm hm2 hear
    (shoelace_ne_zero_of_isSimple (deleteLast R h2)
      (deleteLast_isSimple_of_emptyEar R hS h2 m hm hm2 hear))

/-- **`R.winding = 1` on the open diagonal** (`vₘ → v₀` minus its endpoints). A point
`x` on the closed diagonal that is off `R.boundary` (hence in the relative interior of
the diagonal segment) has `R.winding x = 1`. Proof: the centroid `g` of the open ear
has `R.winding g = 1` (`winding_one_on_open_ear`); the straight segment `[g, x]` lies in
`R.boundaryᶜ` (every point with positive parameter toward `g` is a strict convex
combination of the interior point `g` and the closed-triangle point `x`, hence lies in
`openEar ⊆ R.boundaryᶜ`; the endpoint `x` is off the boundary by hypothesis). `R.winding`
is constant on this preconnected off-boundary segment
(`winding_const_of_isPreconnected`), so `R.winding x = R.winding g = 1`. -/
lemma diagOpen_winding_one (R : LatticePolygon) (hS : R.IsSimple) (hO : R.PositivelyOriented)
    (_ : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) (x : ℝ × ℝ)
    (hxd : x ∈ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)))
    (hxR : x ∉ R.boundary) :
    R.winding x = 1 := by
  classical
  -- generic affine-combination cross identity
  have crosscombo : ∀ (dir base p1 p2 : ℝ × ℝ) (α β : ℝ), α + β = 1 →
      cross dir ((α • p1 + β • p2) - base)
        = α * cross dir (p1 - base) + β * cross dir (p2 - base) := by
    intro dir base p1 p2 α β hαβ
    have hβ : β = 1 - α := by linarith
    subst hβ
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  -- ear-triangle positive orientation: `cross (B-A) (C-A) > 0`
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  have h1 : ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) := by ring
  have hpos : 0 < cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n))) := by
    have key : cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
        (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n)))
        = cornerCross R ((m : ZMod R.n) + 1) := by
      unfold cornerCross; rw [h1, hmp1mp1]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [key]; exact hear.1
  have hcba : cross (toReal (R.vert 0) - toReal (R.vert ((m : ZMod R.n) + 1)))
      (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert ((m : ZMod R.n) + 1)))
      = cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
          (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n))) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  -- the open-ear centroid witness with `R.winding = 1`
  obtain ⟨g, hgmem⟩ := openEar_nonempty R m hm hear
  have hg1 : R.winding g = 1 := winding_one_on_open_ear R hS hO m hm hm2 hear g hgmem
  -- `x` lies in the closed triangle: the three barycentric functionals are `≥ 0`
  obtain ⟨s0, s1, hs0, hs1, hssum, hxeq⟩ := hxd
  have hf1x : 0 ≤ cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
      (x - toReal (R.vert (m : ZMod R.n))) := by
    rw [← hxeq, crosscombo _ _ _ _ s0 s1 hssum]
    have hz0 : cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
        (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert (m : ZMod R.n))) = 0 := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hz0, mul_zero, zero_add]
    exact mul_nonneg hs1 (le_of_lt hpos)
  have hf2x : 0 ≤ cross (toReal (R.vert 0) - toReal (R.vert ((m : ZMod R.n) + 1)))
      (x - toReal (R.vert ((m : ZMod R.n) + 1))) := by
    rw [← hxeq, crosscombo _ _ _ _ s0 s1 hssum]
    have hz1 : cross (toReal (R.vert 0) - toReal (R.vert ((m : ZMod R.n) + 1)))
        (toReal (R.vert 0) - toReal (R.vert ((m : ZMod R.n) + 1))) = 0 := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hz1, mul_zero, add_zero, hcba]
    exact mul_nonneg hs0 (le_of_lt hpos)
  have hf3x : 0 ≤ cross (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0))
      (x - toReal (R.vert 0)) := by
    rw [← hxeq, crosscombo _ _ _ _ s0 s1 hssum]
    have hz0 : cross (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0))
        (toReal (R.vert 0) - toReal (R.vert 0)) = 0 := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    have hz1 : cross (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0))
        (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0)) = 0 := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hz0, hz1]; simp
  -- the segment `[g, x]` lies off `R.boundary`
  have hsub : segment ℝ g x ⊆ R.boundaryᶜ := by
    intro p hp
    obtain ⟨u, vv, hu, hvv, huvsum, hpeq⟩ := hp
    by_cases hu0 : u = 0
    · have hvv1 : vv = 1 := by rw [hu0] at huvsum; linarith
      have hpx : p = x := by rw [← hpeq, hu0, hvv1, zero_smul, one_smul, zero_add]
      rw [Set.mem_compl_iff, hpx]; exact hxR
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hpear : p ∈ openEar R m := by
        rw [← hpeq]
        refine ⟨?_, ?_, ?_⟩
        · rw [crosscombo _ _ _ _ u vv huvsum]
          have := mul_pos hupos hgmem.1
          have := mul_nonneg hvv hf1x
          linarith
        · rw [crosscombo _ _ _ _ u vv huvsum]
          have := mul_pos hupos hgmem.2.1
          have := mul_nonneg hvv hf2x
          linarith
        · rw [crosscombo _ _ _ _ u vv huvsum]
          have := mul_pos hupos hgmem.2.2
          have := mul_nonneg hvv hf3x
          linarith
      exact open_ear_subset_compl_boundary R hS m hm hm2 hear hpear
  -- winding is constant on the segment, so `R.winding x = R.winding g = 1`
  have hconst : R.winding g = R.winding x :=
    winding_const_of_isPreconnected R hsub (convex_segment g x).isPreconnected
      (left_mem_segment ℝ g x) (right_mem_segment ℝ g x)
  rw [← hconst]; exact hg1

/-- **The clip's winding is `0` on the ear legs (the linchpin of `hP1`).** A point `q`
on the ear-triangle boundary (the two legs `[vₘ, vₘ₊₁]`, `[vₘ₊₁, v₀]` or the diagonal)
that lies off the clip's boundary has `(deleteLast R).winding q = 0`. The open-ear
centroid `g` carries `(deleteLast R).winding g = 0` (additivity across the diagonal:
`R.winding g = 1`, `earTri.winding g = 1`, so `clip.winding g = 0`), and the segment
`[g, q]` lies off the clip boundary (the open part is a strict convex combination of the
interior point `g` and the closed-triangle point `q`, hence in
`openEar ⊆ (deleteLast R).boundaryᶜ`; the endpoint `q` is off the clip boundary by
hypothesis). `winding` is constant on this preconnected off-boundary segment, so
`clip.winding q = clip.winding g = 0`. Models `diagOpen_winding_one`. -/
lemma clip_winding_zero_on_legs (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) (q : ℝ × ℝ)
    (hqe : q ∈ (earTri R m hm).boundary)
    (hqc : q ∉ (deleteLast R h2).boundary) :
    (deleteLast R h2).winding q = 0 := by
  classical
  have crosscombo : ∀ (dir base p1 p2 : ℝ × ℝ) (α β : ℝ), α + β = 1 →
      cross dir ((α • p1 + β • p2) - base)
        = α * cross dir (p1 - base) + β * cross dir (p2 - base) := by
    intro dir base p1 p2 α β hαβ
    have hβ : β = 1 - α := by linarith
    subst hβ
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  have h1 : ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) := by ring
  have hpos : 0 < cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n))) := by
    have key : cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
        (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n)))
        = cornerCross R ((m : ZMod R.n) + 1) := by
      unfold cornerCross; rw [h1, hmp1mp1]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [key]; exact hear.1
  -- `q` lies in the closed ear triangle: convexity from the three vertices
  have hqT : inTriangle (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert ((m : ZMod R.n) + 1)))
      (toReal (R.vert 0)) q := by
    have hconv : Convex ℝ {p : ℝ × ℝ | inTriangle (toReal (R.vert (m : ZMod R.n)))
        (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0)) p} := by
      have hset : {p : ℝ × ℝ | inTriangle (toReal (R.vert (m : ZMod R.n)))
          (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0)) p}
          = {p | 0 ≤ cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
                (p - toReal (R.vert (m : ZMod R.n)))}
            ∩ ({p | 0 ≤ cross (toReal (R.vert 0) - toReal (R.vert ((m : ZMod R.n) + 1)))
                (p - toReal (R.vert ((m : ZMod R.n) + 1)))}
              ∩ {p | 0 ≤ cross (toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0))
                (p - toReal (R.vert 0))}) := by
        ext p; simp only [inTriangle, Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [hset]
      exact (convex_nonneg_cross _ _).inter
        ((convex_nonneg_cross _ _).inter (convex_nonneg_cross _ _))
    have ha := inTriangle_fst (toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0)) hpos.le
    have hb := inTriangle_snd (toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0)) hpos.le
    have hc := inTriangle_thd (toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0)) hpos.le
    rw [earTri_boundary_eq R m hm] at hqe
    rcases hqe with (hl0 | hl1) | hd
    · exact hconv.segment_subset ha hb hl0
    · exact hconv.segment_subset hb hc hl1
    · exact hconv.segment_subset hc ha hd
  obtain ⟨hqT1, hqT2, hqT3⟩ := hqT
  -- the open-ear centroid witness carries clip winding `0`
  obtain ⟨g, hgmem⟩ := openEar_nonempty R m hm hear
  have hg0 : (deleteLast R h2).winding g = 0 := by
    have hRg : R.winding g = 1 := winding_one_on_open_ear R hS hO m hm hm2 hear g hgmem
    have hEg : (earTri R m hm).winding g = 1 := openEar_winding_one R m hm hgmem
    have haddg := winding_eq_deleteLast_add_earTri R h2 m hm g
    rw [hRg, hEg] at haddg
    omega
  -- the segment `[g, q]` lies off the clip boundary
  have hsub : segment ℝ g q ⊆ (deleteLast R h2).boundaryᶜ := by
    intro p hp
    obtain ⟨u, vv, hu, hvv, huvsum, hpeq⟩ := hp
    by_cases hu0 : u = 0
    · have hvv1 : vv = 1 := by rw [hu0] at huvsum; linarith
      have hpq : p = q := by rw [← hpeq, hu0, hvv1, zero_smul, one_smul, zero_add]
      rw [Set.mem_compl_iff, hpq]; exact hqc
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hpear : p ∈ openEar R m := by
        rw [← hpeq]
        refine ⟨?_, ?_, ?_⟩
        · rw [crosscombo _ _ _ _ u vv huvsum]
          have := mul_pos hupos hgmem.1
          have := mul_nonneg hvv hqT1
          linarith
        · rw [crosscombo _ _ _ _ u vv huvsum]
          have := mul_pos hupos hgmem.2.1
          have := mul_nonneg hvv hqT2
          linarith
        · rw [crosscombo _ _ _ _ u vv huvsum]
          have := mul_pos hupos hgmem.2.2
          have := mul_nonneg hvv hqT3
          linarith
      exact openEar_subset_clip_compl_boundary R hS h2 m hm hm2 hear hpear
  have hconst : (deleteLast R h2).winding g = (deleteLast R h2).winding q :=
    winding_const_of_isPreconnected (deleteLast R h2) hsub (convex_segment g q).isPreconnected
      (left_mem_segment ℝ g q) (right_mem_segment ℝ g q)
  rw [← hconst]; exact hg0

/-- **Task 1: clip-interior lattice points lie off `R.boundary`.** A clip-interior
lattice point `q` has `clip.winding (toReal q) = 1` and lies off `clip.boundary`. If it
were on `R.boundary` then (since `R.boundary ⊆ clip.boundary ∪ earTri.boundary` via
`boundary_deleteLast_union_earTri`) it would lie on `earTri.boundary`; but
`clip_winding_zero_on_legs` forces `clip.winding (toReal q) = 0` there, contradicting
`= 1`. -/
lemma clip_interiorLattice_subset_R_complBoundary (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    ∀ q ∈ (deleteLast R h2).interiorLattice, toReal q ∉ R.boundary := by
  intro q hq hRb
  simp only [LatticePolygon.interiorLattice, Set.mem_setOf_eq] at hq
  have hmem : toReal q ∈ (deleteLast R h2).boundary ∪ (earTri R m hm).boundary := by
    rw [boundary_deleteLast_union_earTri R h2 m hm]; exact Or.inl hRb
  rcases hmem with hcb | heb
  · exact hq.2 hcb
  · have hz := clip_winding_zero_on_legs R hS hO h2 m hm hm2 hear (toReal q) heb hq.2
    rw [hz] at hq; exact absurd hq.1 (by norm_num)

/-- **Task 2: ear-interior lattice points lie off `R.boundary`.** An ear-interior lattice
point `q` has `earTri.winding (toReal q) = 1` and lies off `earTri.boundary`. The winding
condition forces `toReal q` into the closed triangle (`earTri_winding_zero_of_not_inTriangle`),
and being off the three edges makes the three half-plane tests strict, i.e.
`toReal q ∈ openEar`; the open ear avoids `R.boundary` (`open_ear_subset_compl_boundary`). -/
lemma earTri_interiorLattice_subset_R_complBoundary (R : LatticePolygon) (hS : R.IsSimple)
    (_ : R.PositivelyOriented) (_ : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    ∀ q ∈ (earTri R m hm).interiorLattice, toReal q ∉ R.boundary := by
  intro q hq
  simp only [LatticePolygon.interiorLattice, Set.mem_setOf_eq] at hq
  obtain ⟨hwin, hbd⟩ := hq
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  have h1 : ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) := by ring
  have hpos : 0 < cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n))) := by
    have key : cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
        (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n)))
        = cornerCross R ((m : ZMod R.n) + 1) := by
      unfold cornerCross; rw [h1, hmp1mp1]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [key]; exact hear.1
  -- closed triangle membership from the winding condition
  have hinT : inTriangle (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert ((m : ZMod R.n) + 1)))
      (toReal (R.vert 0)) (toReal q) := by
    by_contra hnot
    have hz := earTri_winding_zero_of_not_inTriangle R m hm hear (toReal q) hnot
    rw [hz] at hwin; exact one_ne_zero hwin.symm
  obtain ⟨hf1, hf2, hf3⟩ := hinT
  rw [earTri_boundary_eq R m hm] at hbd
  -- the three half-plane tests are strict, so `toReal q ∈ openEar`
  have hopen : toReal q ∈ openEar R m := by
    refine ⟨?_, ?_, ?_⟩
    · refine lt_of_le_of_ne hf1 (fun heq => hbd (Or.inl (Or.inl ?_)))
      exact mem_segment_ab_of_inTriangle_f1_zero _ _ _ _ hpos ⟨hf1, hf2, hf3⟩ heq.symm
    · refine lt_of_le_of_ne hf2 (fun heq => hbd (Or.inl (Or.inr ?_)))
      exact mem_segment_bc_of_inTriangle_f2_zero _ _ _ _ hpos ⟨hf1, hf2, hf3⟩ heq.symm
    · refine lt_of_le_of_ne hf3 (fun heq => hbd (Or.inr ?_))
      exact mem_segment_ca_of_inTriangle_f3_zero _ _ _ _ hpos ⟨hf1, hf2, hf3⟩ heq.symm
  exact open_ear_subset_compl_boundary R hS m hm hm2 hear hopen

/-- **Task 3: the interior-lattice partition across the diagonal (`hP1`).** For a simple
positively-oriented `R` with an empty ear at `vₘ₊₁`, the interior lattice splits as the
clip interior, the ear interior, and the open-diagonal lattice points:
`R.interiorLattice = clip.I ⊎ ear.I ⊎ (diagLattice \ R.boundaryLattice)`.

`⊆`: an `R`-interior point either lies on the diagonal (then in `diagLattice` and off
`R.boundaryLattice`) or off it (then `interiorLattice_mem_offDiag` puts it in exactly one
piece). `⊇`: clip- and ear-interior points lie off `R.boundary` (Tasks 1, 2) and off the
diagonal (it is an edge of each piece), so `interiorLattice_mem_offDiag` (with winding
disjointness) places them in `R.interiorLattice`; an open-diagonal point has
`R.winding = 1` (`diagOpen_winding_one`) and is off `R.boundary`. -/
lemma hP1_of_emptyEar (R : LatticePolygon) (hS : R.IsSimple) (hO : R.PositivelyOriented)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    R.interiorLattice =
      (deleteLast R h2).interiorLattice ∪ (earTri R m hm).interiorLattice
        ∪ (diagLattice R m \ R.boundaryLattice) := by
  classical
  have hdS : (deleteLast R h2).IsSimple := deleteLast_isSimple_of_emptyEar R hS h2 m hm hm2 hear
  have hdO : (deleteLast R h2).PositivelyOriented :=
    deleteLast_positivelyOriented_of_emptyEar R hS hO h2 m hm hm2 hear
  have hearS : (earTri R m hm).IsSimple :=
    earTri_isSimple_of_cornerCross_ne R m hm (ne_of_gt hear.1)
  have hearO : (earTri R m hm).PositivelyOriented := earTri_positivelyOriented_of_isEar R m hm hear
  have hdL01 : ∀ p, p ∉ (deleteLast R h2).boundary →
      (deleteLast R h2).winding p = 0 ∨ (deleteLast R h2).winding p = 1 :=
    fun p hp => winding_zero_or_one (deleteLast R h2) hdS hdO p hp
  have hear01 : ∀ p, p ∉ (earTri R m hm).boundary →
      (earTri R m hm).winding p = 0 ∨ (earTri R m hm).winding p = 1 :=
    fun p hp => winding_zero_or_one (earTri R m hm) hearS hearO p hp
  have hdisj := deleteLast_earTri_interiorLattice_disjoint R hS hO h2 m hm
  have hctask1 := clip_interiorLattice_subset_R_complBoundary R hS hO h2 m hm hm2 hear
  have hetask2 := earTri_interiorLattice_subset_R_complBoundary R hS hO h2 m hm hm2 hear
  apply Set.Subset.antisymm
  · -- ⊆
    intro q hq
    simp only [LatticePolygon.interiorLattice, Set.mem_setOf_eq] at hq
    by_cases hqd : toReal q ∈ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
    · refine Or.inr ⟨hqd, ?_⟩
      simp only [LatticePolygon.boundaryLattice, Set.mem_setOf_eq]; exact hq.2
    · have hiff := interiorLattice_mem_offDiag R hS hO h2 m hm hdL01 hear01 q hq.2 hqd
      rcases hiff.mp hq with ⟨hc, _⟩ | ⟨_, he⟩
      · exact Or.inl (Or.inl hc)
      · exact Or.inl (Or.inr he)
  · -- ⊇
    intro q hq
    rcases hq with (hqc | hqe) | hqdiag
    · -- clip interior
      have hqRb : toReal q ∉ R.boundary := hctask1 q hqc
      have hqd : toReal q ∉ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) :=
        fun hd => hqc.2 (diag_subset_deleteLast_boundary R h2 m hm hd)
      exact (interiorLattice_mem_offDiag R hS hO h2 m hm hdL01 hear01 q hqRb hqd).mpr
        (Or.inl ⟨hqc, Set.disjoint_left.mp hdisj hqc⟩)
    · -- ear interior
      have hqRb : toReal q ∉ R.boundary := hetask2 q hqe
      have hqd : toReal q ∉ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) :=
        fun hd => hqe.2 (diag_subset_earTri_boundary R m hm hd)
      exact (interiorLattice_mem_offDiag R hS hO h2 m hm hdL01 hear01 q hqRb hqd).mpr
        (Or.inr ⟨Set.disjoint_right.mp hdisj hqe, hqe⟩)
    · -- open diagonal
      obtain ⟨hqD, hqB⟩ := hqdiag
      have hqRb : toReal q ∉ R.boundary := by
        simp only [LatticePolygon.boundaryLattice, Set.mem_setOf_eq] at hqB; exact hqB
      have hqD' : toReal q ∈ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := hqD
      exact ⟨diagOpen_winding_one R hS hO h2 m hm hm2 hear (toReal q) hqD' hqRb, hqRb⟩

/-- **Task 4: the `I,B` lattice-count additivity for an empty ear (`hIB`, conjunct 6).**
Feed the three diagonal-partition facts (`hP1_of_emptyEar`, `hP2_of_emptyEar`,
`hP3_of_emptyEar`) into the combinatorial assembler `hIB_of_partition`. -/
lemma hIB_of_emptyEar (R : LatticePolygon) (hS : R.IsSimple) (hO : R.PositivelyOriented)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    (R.I : ℝ) + (R.B : ℝ) / 2 = ((deleteLast R h2).I : ℝ) + ((earTri R m hm).I : ℝ)
      + (((deleteLast R h2).B : ℝ) + ((earTri R m hm).B : ℝ)) / 2 - 1 :=
  hIB_of_partition R hS hO h2 m hm
    (earTri_isSimple_of_cornerCross_ne R m hm (ne_of_gt hear.1))
    (hP1_of_emptyEar R hS hO h2 m hm hm2 hear)
    (hP2_of_emptyEar R hS h2 m hm hm2 hear)
    (hP3_of_emptyEar R hS m hm hm2 hear)

/-- **`ValidEarLast` from an empty ear at the last vertex (all six conjuncts landed).**
Given an empty ear `isEarVertex R ((m : ZMod R.n)+1)` with `R.n = m+2`, `m ≥ 2`, every
conjunct of `ValidEarLast R` is now discharged Hopf-free: clip simplicity
(`deleteLast_isSimple_of_emptyEar`), clip orientation
(`deleteLast_positivelyOriented_of_emptyEar`), ear simplicity/orientation (inside
`validEarLast_of_ear`), off-boundary winding disjointness
(`earTri_disjoint_winding_offBoundary`), and the `I,B` count (`hIB_of_emptyEar`). Hence
the entire ear-clipping split reduces to *finding an empty ear at the last vertex*. -/
lemma validEarLast_of_emptyEar (R : LatticePolygon) (hS : R.IsSimple)
    (hO : R.PositivelyOriented) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    ValidEarLast R :=
  validEarLast_of_ear R hS h2 m hm hear
    (deleteLast_isSimple_of_emptyEar R hS h2 m hm hm2 hear)
    (deleteLast_positivelyOriented_of_emptyEar R hS hO h2 m hm hm2 hear)
    (fun q hqb => earTri_disjoint_winding_offBoundary R hS hO h2 m hm q hqb)
    (hIB_of_emptyEar R hS hO h2 m hm hm2 hear)

/-- **`EarProvider` from bare ear-vertex existence (rotation bookkeeping).** Given that
every simple, positively-oriented polygon with `≥ 4` vertices has *some* ear vertex
(`exists_ear`, the Meisters two-ears content), rotate it so that the ear lands at the last
index `m+1` (`m+2 = n`); then `validEarLast_of_emptyEar` packages the entire ear-clipping
split (clip simplicity/orientation, ear simplicity/orientation, off-boundary winding
disjointness, `I,B` additivity). This is the single step between bare ear existence and
`EarProvider`, hence Pick's theorem via `pick_of_provider`. -/
lemma earProvider_of_exists_ear
    (hex : ∀ Q : LatticePolygon, Q.IsSimple → Q.PositivelyOriented → 4 ≤ Q.n →
      ∃ i : ZMod Q.n, isEarVertex Q i) :
    EarProvider := by
  intro Q hS hO hn
  obtain ⟨i, hi⟩ := hex Q hS hO hn
  -- the clipped vertex count `m` (so `m + 2 = Q.n`, `m ≥ 2`); `m` is kept opaque
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Q.n = m + 2 := ⟨Q.n - 2, by omega⟩
  have hm2 : 2 ≤ m := by omega
  -- rotation amount `c` carrying the ear vertex `i` to the last index `m+1` (opaque)
  obtain ⟨c, hc⟩ : ∃ c : ZMod Q.n, ((m : ZMod Q.n) + 1) + c = i :=
    ⟨i - ((m : ZMod Q.n) + 1), by ring⟩
  have h2 : 2 ≤ (rotateP Q c).n := by rw [rotateP_n]; omega
  have hmR : (rotateP Q c).n = m + 2 := by rw [rotateP_n]; exact hm
  have hRS : (rotateP Q c).IsSimple := isSimple_rotateP Q c hS
  have hRO : (rotateP Q c).PositivelyOriented := positivelyOriented_rotateP Q c hO
  -- Transport the ear across the rotation via the iff (no type ascription on the index, so
  -- the numeral is elaborated in `ZMod Q.n` rather than forcing instance search on the
  -- not-yet-reduced `ZMod (rotateP Q c).n`).
  have hear := (isEarVertex_rotateP Q c ((m : ZMod Q.n) + 1)).mpr (by rw [hc]; exact hi)
  exact ⟨c, validEarLast_of_emptyEar (rotateP Q c) hRS hRO h2 m hmR hm2 hear⟩

/-! ### Diagonals and the closest-contained-vertex selection (front half of `exists_diagonal`)

Toward `exists_ear` (O'Rourke Theorem 1.4) we follow Lemma 1.3: from a convex vertex
`v = vₖ` (neighbours `a = vₖ₋₁`, `b = vₖ₊₁`), either the closed corner triangle `(a,v,b)`
contains no other polygon vertex — in which case `v` is already an ear — or, among the
contained vertices, the one `w` **closest to `v`** spans a diagonal `[v, w]`. Here we land
the purely-combinatorial selection (`Finset.exists_min_image`) and the convex/empty
dichotomy. The geometric crux (`[v,w]` meets no edge) and the polygon split are separate. -/

/-- The (open) segment `(vᵢ, vⱼ)` is a **diagonal**: `i, j` are non-adjacent and the open
segment meets no edge of the polygon. This is exactly what the polygon split needs to
inherit simplicity. -/
def IsDiagonal (P : LatticePolygon) (i j : ZMod P.n) : Prop :=
  i ≠ j ∧ i + 1 ≠ j ∧ j + 1 ≠ i ∧
    ∀ k : ZMod P.n,
      Disjoint (openSegment ℝ (toReal (P.vert i)) (toReal (P.vert j))) (P.edgeSeg k)

/-- **Depth** of a point `x` below the base line `(vᵢ₋₁, vᵢ₊₁)` of the corner triangle at
`i`, toward the apex `vᵢ`. Equals the third `inTriangle` half-plane functional
`cross (vᵢ₋₁ − vᵢ₊₁) (x − vᵢ₊₁)`; it is `0` on the base line, `cornerCross`-positive at the
apex, and `≥ 0` throughout the (CCW) corner triangle. The **deepest** contained vertex is the
one maximizing this. -/
def cornerDepth (P : LatticePolygon) (i : ZMod P.n) (x : ℝ × ℝ) : ℝ :=
  cross (toReal (P.vert (i - 1)) - toReal (P.vert (i + 1))) (x - toReal (P.vert (i + 1)))

/-- **Deepest contained vertex.** If the closed corner triangle `(vᵢ₋₁, vᵢ, vᵢ₊₁)` contains
some polygon vertex other than the three corners, then it contains one, `w`, of maximal
`cornerDepth` (depth toward the apex `vᵢ`). This `w` is the vertex de Berg joins to `vᵢ` to
form a diagonal: nothing strictly deeper than `w`'s parallel-to-base line contains a vertex. -/
lemma exists_deepest_contained (P : LatticePolygon) (i : ZMod P.n)
    (hne : ∃ j : ZMod P.n, j ≠ i - 1 ∧ j ≠ i ∧ j ≠ i + 1 ∧
      inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
        (toReal (P.vert j))) :
    ∃ w : ZMod P.n,
      (w ≠ i - 1 ∧ w ≠ i ∧ w ≠ i + 1 ∧
        inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
          (toReal (P.vert w))) ∧
      ∀ j : ZMod P.n, j ≠ i - 1 → j ≠ i → j ≠ i + 1 →
        inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
          (toReal (P.vert j)) →
        cornerDepth P i (toReal (P.vert j)) ≤ cornerDepth P i (toReal (P.vert w)) := by
  classical
  set S : Finset (ZMod P.n) :=
    Finset.univ.filter (fun j => j ≠ i - 1 ∧ j ≠ i ∧ j ≠ i + 1 ∧
      inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
        (toReal (P.vert j))) with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨j, by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨w, hwS, hwmax⟩ :=
    Finset.exists_max_image S (fun j => cornerDepth P i (toReal (P.vert j))) hSne
  rw [hSdef, Finset.mem_filter] at hwS
  refine ⟨w, hwS.2, ?_⟩
  intro j hj1 hj2 hj3 hjT
  exact hwmax j (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj1, hj2, hj3, hjT⟩)

/-- **Convex/empty dichotomy via the deepest vertex.** A simple positively-oriented polygon
either already has an ear vertex, or it has a convex vertex `i` together with the *deepest*
contained vertex `w` of its corner triangle. In the second case `[vᵢ, v_w]` is the de Berg
diagonal candidate. -/
lemma exists_ear_or_deepestContained (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) :
    (∃ i : ZMod P.n, isEarVertex P i) ∨
    (∃ i w : ZMod P.n, 0 < cornerCross P i ∧
      (w ≠ i - 1 ∧ w ≠ i ∧ w ≠ i + 1 ∧
        inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
          (toReal (P.vert w))) ∧
      ∀ j : ZMod P.n, j ≠ i - 1 → j ≠ i → j ≠ i + 1 →
        inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
          (toReal (P.vert j)) →
        cornerDepth P i (toReal (P.vert j)) ≤ cornerDepth P i (toReal (P.vert w))) := by
  classical
  obtain ⟨i, hconv⟩ := exists_convex_vertex P hS hO
  by_cases hemp : ∃ j : ZMod P.n, j ≠ i - 1 ∧ j ≠ i ∧ j ≠ i + 1 ∧
      inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
        (toReal (P.vert j))
  · right
    obtain ⟨w, hw, hwmax⟩ := exists_deepest_contained P i hemp
    exact ⟨i, w, hconv, hw, hwmax⟩
  · left
    push Not at hemp
    exact ⟨i, isEarVertex_of_empty P i hconv hemp⟩

/-! ### The deep sub-triangle crossing lemma (geometric heart of `deepest_contained_isDiagonal`)

For the de Berg diagonal `[vᵢ, v_w]` (apex `b = vᵢ`, `w` the deepest contained vertex), every
interior point of the open diagonal lies in the open **deep sub-triangle**
`Δ = {f₁ > 0, f₂ > 0, f₃ > d}` of the corner triangle `(a, b, c)` (`a = vᵢ₋₁`, `c = vᵢ₊₁`,
`d = cornerDepth(v_w)`).  If a polygon edge `[e₀, e₁]` met such a point, then walking toward
the *deeper* endpoint either crosses a leg `[a,b]` / `[b,c]` of the corner triangle (at a
point still strictly deeper than `d`, ruling out the base corners `a`, `c`), or that endpoint
is itself a vertex strictly deeper than `w` — which maximality forces to be the apex.  This is
the deep-triangle analogue of `Pick.segment_meets_leg_of_cross_base`. -/

/-- Affine-along-a-segment for a planar cross functional (local copy of the EarClip helper). -/
private lemma cross_affine_seg' (u w e0 e1 : ℝ × ℝ) (s : ℝ) :
    cross u (((1 - s) • e0 + s • e1) - w)
      = (1 - s) * cross u (e0 - w) + s * cross u (e1 - w) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- First-exit on a segment for two affine functionals (local copy of the EarClip helper). -/
private lemma first_exit_two_affine' (α1 β1 α2 β2 : ℝ)
    (hα1 : 0 < α1) (hα2 : 0 < α2) (hβ : β1 < 0 ∨ β2 < 0) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧ 0 ≤ (1 - u) * α1 + u * β1 ∧ 0 ≤ (1 - u) * α2 + u * β2 ∧
      ((1 - u) * α1 + u * β1 = 0 ∨ (1 - u) * α2 + u * β2 = 0) := by
  set u1 : ℝ := if β1 < 0 then α1 / (α1 - β1) else 1 with hu1
  set u2 : ℝ := if β2 < 0 then α2 / (α2 - β2) else 1 with hu2
  have hu1pos : 0 < u1 := by
    rw [hu1]; split_ifs with h
    · exact div_pos hα1 (by linarith)
    · norm_num
  have hu2pos : 0 < u2 := by
    rw [hu2]; split_ifs with h
    · exact div_pos hα2 (by linarith)
    · norm_num
  have hu1le : u1 ≤ 1 := by
    rw [hu1]; split_ifs with h
    · rw [div_le_one (by linarith)]; linarith
    · exact le_refl 1
  have hu2le : u2 ≤ 1 := by
    rw [hu2]; split_ifs with h
    · rw [div_le_one (by linarith)]; linarith
    · exact le_refl 1
  have hval1 : ∀ u, 0 ≤ u → u ≤ u1 → 0 ≤ (1 - u) * α1 + u * β1 := by
    intro u hu0 huu
    rcases le_or_gt (0:ℝ) β1 with hb | hb
    · nlinarith [hu0]
    · rw [hu1, if_pos hb] at huu
      have hden : 0 < α1 - β1 := by linarith
      rw [le_div_iff₀ hden] at huu; nlinarith
  have hval2 : ∀ u, 0 ≤ u → u ≤ u2 → 0 ≤ (1 - u) * α2 + u * β2 := by
    intro u hu0 huu
    rcases le_or_gt (0:ℝ) β2 with hb | hb
    · nlinarith [hu0]
    · rw [hu2, if_pos hb] at huu
      have hden : 0 < α2 - β2 := by linarith
      rw [le_div_iff₀ hden] at huu; nlinarith
  have hz1 : β1 < 0 → (1 - u1) * α1 + u1 * β1 = 0 := by
    intro hb; rw [hu1, if_pos hb]
    have hden : α1 - β1 ≠ 0 := ne_of_gt (by linarith)
    field_simp; ring
  have hz2 : β2 < 0 → (1 - u2) * α2 + u2 * β2 = 0 := by
    intro hb; rw [hu2, if_pos hb]
    have hden : α2 - β2 ≠ 0 := ne_of_gt (by linarith)
    field_simp; ring
  rcases le_total u1 u2 with hle | hle
  · rcases le_or_gt (0:ℝ) β1 with hb1 | hb1
    · have hb2 : β2 < 0 := hβ.resolve_left (by simpa using hb1)
      have hu1one : u1 = 1 := by rw [hu1, if_neg (by simpa using hb1)]
      have : u2 = 1 := le_antisymm hu2le (hu1one ▸ hle)
      refine ⟨u2, hu2pos, hu2le, ?_, ?_, Or.inr (hz2 hb2)⟩
      · exact hval1 u2 hu2pos.le (by rw [this, hu1one])
      · exact hval2 u2 hu2pos.le (le_refl u2)
    · refine ⟨u1, hu1pos, hu1le, le_of_eq (hz1 hb1).symm, hval2 u1 hu1pos.le hle, Or.inl (hz1 hb1)⟩
  · rcases le_or_gt (0:ℝ) β2 with hb2 | hb2
    · have hb1 : β1 < 0 := hβ.resolve_right (by simpa using hb2)
      have hu2one : u2 = 1 := by rw [hu2, if_neg (by simpa using hb2)]
      have : u1 = 1 := le_antisymm hu1le (hu2one ▸ hle)
      refine ⟨u1, hu1pos, hu1le, ?_, ?_, Or.inl (hz1 hb1)⟩
      · exact hval1 u1 hu1pos.le (le_refl u1)
      · exact hval2 u1 hu1pos.le (by rw [this, hu2one])
    · refine ⟨u2, hu2pos, hu2le, hval1 u2 hu2pos.le hle, le_of_eq (hz2 hb2).symm, Or.inr (hz2 hb2)⟩

/-- **Deep sub-triangle crossing lemma.**  Triangle `(a, b, c)` positively oriented, base
depth `d ≥ 0`.  If a point `p` of the segment `[e₀, e₁]` lies in the open deep sub-triangle
`Δ` (`f₁ p > 0`, `f₂ p > 0`, `f₃ p > d` with `f₁ x = cross (b−a) (x−a)`,
`f₂ x = cross (c−b) (x−b)`, `f₃ x = cross (a−c) (x−c)`), then `[e₀, e₁]` either meets a leg
`[a, b]` or `[b, c]` of the triangle at a point still strictly deeper than `d`, or one of its
endpoints lies in the closed triangle strictly deeper than `d`. -/
private lemma deep_seg_meets_leg (a b c : ℝ × ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hbase : 0 < cross (b - a) (c - a)) (e0 e1 p : ℝ × ℝ)
    (hf1p : 0 < cross (b - a) (p - a)) (hf2p : 0 < cross (c - b) (p - b))
    (hf3p : d < cross (a - c) (p - c)) (hpseg : p ∈ segment ℝ e0 e1) :
    (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ a b ∧ d < cross (a - c) (q - c)) ∨
    (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ b c ∧ d < cross (a - c) (q - c)) ∨
    (∃ e, (e = e0 ∨ e = e1) ∧ inTriangle a b c e ∧ d < cross (a - c) (e - c)) := by
  set f1 : ℝ × ℝ → ℝ := fun x => cross (b - a) (x - a) with hf1
  set f2 : ℝ × ℝ → ℝ := fun x => cross (c - b) (x - b) with hf2
  set f3 : ℝ × ℝ → ℝ := fun x => cross (a - c) (x - c) with hf3
  have hinTri : ∀ x, inTriangle a b c x ↔ 0 ≤ f1 x ∧ 0 ≤ f2 x ∧ 0 ≤ f3 x := fun x => Iff.rfl
  -- p = (1-s) e0 + s e1
  rw [segment_eq_image] at hpseg
  obtain ⟨s, ⟨hs0, hs1⟩, hps⟩ := hpseg
  have hps' : p = (1 - s) • e0 + s • e1 := by rw [← hps]
  have hf3s : f3 p = (1 - s) * f3 e0 + s * f3 e1 := by rw [hf3, hps']; exact cross_affine_seg' _ _ _ _ _
  -- a deeper endpoint exists
  have hdeep : d < f3 e0 ∨ d < f3 e1 := by
    by_contra hc; push Not at hc
    have hle : f3 p ≤ d := by
      rw [hf3s]
      nlinarith [mul_le_mul_of_nonneg_left hc.1 (by linarith : (0:ℝ) ≤ 1 - s),
        mul_le_mul_of_nonneg_left hc.2 hs0]
    have hp3 : d < f3 p := hf3p
    linarith
  -- handle a single deep endpoint e
  have he0seg : e0 ∈ segment ℝ e0 e1 := left_mem_segment ℝ e0 e1
  have he1seg : e1 ∈ segment ℝ e0 e1 := right_mem_segment ℝ e0 e1
  have key : ∀ e : ℝ × ℝ, (e = e0 ∨ e = e1) → e ∈ segment ℝ e0 e1 → d < f3 e →
      (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ a b ∧ d < cross (a - c) (q - c)) ∨
      (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ b c ∧ d < cross (a - c) (q - c)) ∨
      (∃ e', (e' = e0 ∨ e' = e1) ∧ inTriangle a b c e' ∧ d < cross (a - c) (e' - c)) := by
    intro e he01 heseg hf3e
    have hf3enn : 0 ≤ f3 e := le_trans hd (le_of_lt hf3e)
    by_cases hin : inTriangle a b c e
    · exact Or.inr (Or.inr ⟨e, he01, hin, by rw [hf3] at hf3e; exact hf3e⟩)
    · -- e outside triangle, f3 e ≥ 0 ⟹ f1 e < 0 ∨ f2 e < 0
      have hβ : f1 e < 0 ∨ f2 e < 0 := by
        by_contra hc; push Not at hc
        exact hin ((hinTri e).mpr ⟨hc.1, hc.2, hf3enn⟩)
      obtain ⟨u, hu0, _, hv1, hv2, hzero⟩ :=
        first_exit_two_affine' (f1 p) (f1 e) (f2 p) (f2 e) hf1p hf2p hβ
      set z := (1 - u) • p + u • e with hzdef
      have hpseg' : p ∈ segment ℝ e0 e1 := ⟨1 - s, s, by linarith, hs0, by ring, by rw [← hps']⟩
      have hzseg : z ∈ segment ℝ e0 e1 :=
        convex_segment e0 e1 hpseg' heseg (by linarith) hu0.le (by ring)
      have hf1z : f1 z = (1 - u) * f1 p + u * f1 e := by rw [hf1, hzdef]; exact cross_affine_seg' _ _ _ _ _
      have hf2z : f2 z = (1 - u) * f2 p + u * f2 e := by rw [hf2, hzdef]; exact cross_affine_seg' _ _ _ _ _
      have hf3z : f3 z = (1 - u) * f3 p + u * f3 e := by rw [hf3, hzdef]; exact cross_affine_seg' _ _ _ _ _
      have hf3zd : d < f3 z := by
        have hp3 : d < f3 p := hf3p
        rw [hf3z]
        nlinarith [mul_pos hu0 (by linarith : (0:ℝ) < f3 e - d),
          mul_nonneg (by linarith : (0:ℝ) ≤ 1 - u) (by linarith : (0:ℝ) ≤ f3 p - d)]
      have hzT : inTriangle a b c z :=
        (hinTri z).mpr ⟨by rw [hf1z]; exact hv1, by rw [hf2z]; exact hv2, le_trans hd hf3zd.le⟩
      rcases hzero with h0 | h0
      · exact Or.inl ⟨z, hzseg,
          mem_segment_ab_of_inTriangle_f1_zero a b c z hbase hzT (by rw [← hf1z] at h0; exact h0),
          by rw [hf3] at hf3zd; exact hf3zd⟩
      · exact Or.inr (Or.inl ⟨z, hzseg,
          mem_segment_bc_of_inTriangle_f2_zero a b c z hbase hzT (by rw [← hf2z] at h0; exact h0),
          by rw [hf3] at hf3zd; exact hf3zd⟩)
  rcases hdeep with h | h
  · exact key e0 (Or.inl rfl) he0seg h
  · exact key e1 (Or.inr rfl) he1seg h

/-- **The de Berg diagonal.** For a convex vertex `i` (`0 < cornerCross P i`) and the
*deepest* contained vertex `w` of its corner triangle, the open segment `[vᵢ, v_w]` is a
diagonal: it is non-adjacent and meets no polygon edge. Every interior point lies in the open
deep sub-triangle `Δ`; an edge meeting it would (via `deep_seg_meets_leg`) cross a leg of the
corner triangle at a point strictly deeper than `v_w` — impossible by simplicity and the base
corners' zero depth — or have a vertex strictly deeper than `v_w`, which maximality forces to
be the apex `vᵢ` (incident, excluded). -/
lemma deepest_contained_isDiagonal (P : LatticePolygon) (hS : P.IsSimple) (i w : ZMod P.n)
    (hconv : 0 < cornerCross P i)
    (hw1 : w ≠ i - 1) (hw2 : w ≠ i) (hw3 : w ≠ i + 1)
    (hwT : inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
            (toReal (P.vert w)))
    (hwmax : ∀ j : ZMod P.n, j ≠ i - 1 → j ≠ i → j ≠ i + 1 →
        inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
          (toReal (P.vert j)) →
        cornerDepth P i (toReal (P.vert j)) ≤ cornerDepth P i (toReal (P.vert w))) :
    IsDiagonal P i w := by
  classical
  set a := toReal (P.vert (i - 1)) with ha
  set b := toReal (P.vert i) with hb
  set c := toReal (P.vert (i + 1)) with hc
  set vw := toReal (P.vert w) with hvw
  set d := cornerDepth P i vw with hd_def
  -- D₀ = cornerCross = cross (b-a) (c-a)
  have hbase : 0 < cross (b - a) (c - a) := by
    have h := hconv
    simp only [cornerCross] at h
    rw [← ha, ← hb, ← hc] at h
    have e : cross (b - a) (c - b) = cross (b - a) (c - a) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e] at h; exact h
  -- d as the third functional at vw
  have hd : d = cross (a - c) (vw - c) := by
    rw [hd_def]; simp only [cornerDepth]; rw [← ha, ← hc]
  obtain ⟨hw1nn, hw2nn, hw3nn⟩ := hwT
  have hdnn : 0 ≤ d := by rw [hd]; exact hw3nn
  -- f1 vw, f2 vw strictly positive (else vw on a leg edge)
  have hf1w : 0 < cross (b - a) (vw - a) := by
    rcases lt_or_eq_of_le hw1nn with h | h
    · exact h
    · exfalso
      have hmem : vw ∈ segment ℝ a b :=
        mem_segment_ab_of_inTriangle_f1_zero a b c vw hbase ⟨hw1nn, hw2nn, hw3nn⟩ h.symm
      have hedge : P.edgeSeg (i - 1) = segment ℝ a b := by
        rw [LatticePolygon.edgeSeg, show (i - 1) + 1 = i by ring, ← ha, ← hb]
      exact vert_notMem_edgeSeg P hS w (i - 1) (Ne.symm hw1)
        (fun he => hw2 (by linear_combination -he)) (hedge ▸ hmem)
  have hf2w : 0 < cross (c - b) (vw - b) := by
    rcases lt_or_eq_of_le hw2nn with h | h
    · exact h
    · exfalso
      have hmem : vw ∈ segment ℝ b c :=
        mem_segment_bc_of_inTriangle_f2_zero a b c vw hbase ⟨hw1nn, hw2nn, hw3nn⟩ h.symm
      have hedge : P.edgeSeg i = segment ℝ b c := by
        rw [LatticePolygon.edgeSeg, ← hb, ← hc]
      exact vert_notMem_edgeSeg P hS w i (Ne.symm hw2)
        (fun he => hw3 (by linear_combination -he)) (hedge ▸ hmem)
  -- d < D₀ (barycentric, since f1 vw, f2 vw > 0)
  have hbary : cross (b - a) (vw - a) + cross (c - b) (vw - b) + cross (a - c) (vw - c)
      = cross (b - a) (c - a) := by simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hdD0 : d < cross (b - a) (c - a) := by rw [hd]; linarith [hf1w, hf2w, hbary]
  -- maximality in the cone: an inTriangle vertex strictly deeper than vw is the apex
  have hmaxcone : ∀ j : ZMod P.n,
      inTriangle a b c (toReal (P.vert j)) → d < cross (a - c) (toReal (P.vert j) - c) →
      toReal (P.vert j) = b := by
    intro j hjT hjf3
    by_cases hj1 : j = i - 1
    · exfalso; rw [hj1, ← ha, cross_self] at hjf3; linarith [hdnn]
    by_cases hj2 : j = i
    · rw [hj2]
    by_cases hj3 : j = i + 1
    · exfalso; rw [hj3, ← hc] at hjf3
      rw [show cross (a - c) (c - c) = 0 by simp [cross]] at hjf3; linarith [hdnn]
    · exfalso
      have hmax := hwmax j hj1 hj2 hj3 hjT
      have hcd : cornerDepth P i (toReal (P.vert j)) = cross (a - c) (toReal (P.vert j) - c) := by
        simp only [cornerDepth]; rw [← ha, ← hc]
      rw [hcd] at hmax; linarith
  refine ⟨Ne.symm hw2, Ne.symm hw3, fun he => hw1 (by linear_combination he), ?_⟩
  intro k
  rw [Set.disjoint_left]
  intro p hpD hpk
  -- p ∈ Δ : f1 p > 0, f2 p > 0, f3 p > d
  rw [openSegment_eq_image] at hpD
  obtain ⟨t, ⟨ht0, ht1⟩, hpt⟩ := hpD
  have hpb : p = (1 - t) • b + t • vw := by rw [← hpt]
  have hf1pe : cross (b - a) (p - a) = t * cross (b - a) (vw - a) := by
    rw [hpb]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hf2pe : cross (c - b) (p - b) = t * cross (c - b) (vw - b) := by
    rw [hpb]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hf3pe : cross (a - c) (p - c)
      = (1 - t) * cross (a - c) (b - c) + t * cross (a - c) (vw - c) := by
    rw [hpb]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hf3b : cross (a - c) (b - c) = cross (b - a) (c - a) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hf1p : 0 < cross (b - a) (p - a) := by rw [hf1pe]; exact mul_pos ht0 hf1w
  have hf2p : 0 < cross (c - b) (p - b) := by rw [hf2pe]; exact mul_pos ht0 hf2w
  have hf3p : d < cross (a - c) (p - c) := by
    rw [hf3pe, hf3b, ← hd]
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - t) (by linarith : (0:ℝ) < cross (b - a) (c - a) - d)]
  -- dispatch on k
  by_cases hki1 : k = i - 1
  · -- leg [a,b]: p on it ⟹ f1 p = 0, contra
    subst hki1
    rw [LatticePolygon.edgeSeg, show (i - 1) + 1 = i by ring, ← ha, ← hb] at hpk
    obtain ⟨x, y, hx, hy, hxy, hp⟩ := hpk
    have hx1 : x = 1 - y := by linarith
    have h0 : cross (b - a) (p - a) = 0 := by
      rw [← hp, hx1]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    linarith [hf1p]
  by_cases hki : k = i
  · -- leg [b,c]: p on it ⟹ f2 p = 0, contra
    subst hki
    rw [LatticePolygon.edgeSeg, ← hb, ← hc] at hpk
    obtain ⟨x, y, hx, hy, hxy, hp⟩ := hpk
    have hx1 : x = 1 - y := by linarith
    have h0 : cross (c - b) (p - b) = 0 := by
      rw [← hp, hx1]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    linarith [hf2p]
  · -- non-incident to apex: crossing lemma
    have hpkseg : p ∈ segment ℝ (toReal (P.vert k)) (toReal (P.vert (k + 1))) := by
      rw [LatticePolygon.edgeSeg] at hpk; exact hpk
    have hcross := deep_seg_meets_leg a b c d hdnn hbase
      (toReal (P.vert k)) (toReal (P.vert (k + 1))) p hf1p hf2p hf3p hpkseg
    rcases hcross with ⟨q, hqseg, hqab, hqf3⟩ | ⟨q, hqseg, hqbc, hqf3⟩ | ⟨e, he01, hin, hef3⟩
    · -- meets leg [a,b] = edgeSeg (i-1)
      have hqk : q ∈ P.edgeSeg k := by rw [LatticePolygon.edgeSeg]; exact hqseg
      have hqe : q ∈ P.edgeSeg (i - 1) := by
        rw [LatticePolygon.edgeSeg, show (i - 1) + 1 = i by ring, ← ha, ← hb]; exact hqab
      by_cases hadj : k = i - 2
      · subst hadj
        have hsing := hS.2.2 (i - 2)
        rw [show (i - 2) + 1 = i - 1 by ring] at hsing
        have hqmem : q ∈ P.edgeSeg (i - 2) ∩ P.edgeSeg (i - 1) := ⟨hqk, hqe⟩
        rw [hsing] at hqmem
        rw [Set.mem_singleton_iff] at hqmem
        have hqa : q = a := by rw [hqmem]
        rw [hqa, cross_self] at hqf3; linarith [hdnn]
      · have hdisj : Disjoint (P.edgeSeg (i - 1)) (P.edgeSeg k) :=
          hS.2.1 (i - 1) k (fun h => hki1 h.symm)
            (by rw [show (i - 1) + 1 = i by ring]; exact Ne.symm hki)
            (fun he => hadj (by linear_combination he))
        exact Set.disjoint_left.mp hdisj hqe hqk
    · -- meets leg [b,c] = edgeSeg i
      have hqk : q ∈ P.edgeSeg k := by rw [LatticePolygon.edgeSeg]; exact hqseg
      have hqi : q ∈ P.edgeSeg i := by rw [LatticePolygon.edgeSeg, ← hb, ← hc]; exact hqbc
      by_cases hadj : k = i + 1
      · subst hadj
        have hsing := hS.2.2 i
        have hqmem : q ∈ P.edgeSeg i ∩ P.edgeSeg (i + 1) := ⟨hqi, hqk⟩
        rw [hsing] at hqmem
        rw [Set.mem_singleton_iff] at hqmem
        have hqc : q = c := by rw [hqmem]
        rw [hqc] at hqf3
        have : cross (a - c) (c - c) = 0 := by simp [cross]
        rw [this] at hqf3; linarith [hdnn]
      · have hdisj : Disjoint (P.edgeSeg i) (P.edgeSeg k) :=
          hS.2.1 i k (Ne.symm hki) (fun h => hadj h.symm)
            (fun he => hki1 (by linear_combination he))
        exact Set.disjoint_left.mp hdisj hqi hqk
    · -- deep endpoint in triangle ⟹ apex ⟹ k incident to apex, excluded
      rcases he01 with he | he
      · have hbe : toReal (P.vert k) = b :=
          hmaxcone k (by rw [← he]; exact hin) (by rw [← he]; exact hef3)
        exact hki (vert_injective P hS (toReal_injective (by rw [hbe, hb])))
      · have hbe : toReal (P.vert (k + 1)) = b :=
          hmaxcone (k + 1) (by rw [← he]; exact hin) (by rw [← he]; exact hef3)
        have hk1i : k + 1 = i := vert_injective P hS (toReal_injective (by rw [hbe, hb]))
        exact hki1 (by linear_combination hk1i)

/-- **Existence of an ear or a diagonal** (front half of O'Rourke's Theorem 1.4). A simple,
positively-oriented polygon with at least `4` vertices either has an ear vertex outright, or
admits a diagonal `[vᵢ, v_w]` (`i` convex, `w` deepest contained), via
`deepest_contained_isDiagonal`. -/
lemma exists_diagonal (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (_ : 4 ≤ P.n) :
    (∃ i : ZMod P.n, isEarVertex P i) ∨
      (∃ i j : ZMod P.n, IsDiagonal P i j ∧ 0 < cornerCross P i) := by
  rcases exists_ear_or_deepestContained P hS hO with hear | ⟨i, w, hconv, ⟨hw1, hw2, hw3, hwT⟩, hwmax⟩
  · exact Or.inl hear
  · exact Or.inr ⟨i, w, deepest_contained_isDiagonal P hS i w hconv hw1 hw2 hw3 hwT hwmax, hconv⟩

/-! ### Polygon split across a diagonal: the definitions and vertex-count arithmetic

Given a diagonal `(i, j)`, the **forward-arc sub-polygon** `splitPoly P i j` has vertices
`vᵢ, vᵢ₊₁, …, vⱼ` (the arc from `i` to `j`), closed by the diagonal edge `vⱼ → vᵢ`. The two
halves of O'Rourke's split are `splitPoly P i j` and `splitPoly P j i`; together they have
`P.n + 2` vertices (the diagonal is shared) and each has strictly fewer than `P.n` (and at
least `3`) when `(i, j)` is non-adjacent. The harder `IsSimple` / `PositivelyOriented`
inheritance is deferred. -/

/-- A small `ZMod` fact: for a nonzero element, the values of `x` and `-x` sum to `n`. -/
lemma val_add_val_neg (n : ℕ) [NeZero n] (x : ZMod n) (hx : x ≠ 0) :
    x.val + (-x).val = n := by
  rw [ZMod.neg_val, if_neg hx]
  have : x.val < n := ZMod.val_lt x
  omega

/-- For `n ≥ 2`, an element of `ZMod n` that is neither `0` nor `1` has value `≥ 2`. -/
lemma two_le_val (n : ℕ) [NeZero n] (_ : 2 ≤ n) (x : ZMod n) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    2 ≤ x.val := by
  have hv0 : x.val ≠ 0 := by rw [Ne, ZMod.val_eq_zero]; exact h0
  have hv1 : x.val ≠ 1 := by
    intro hc
    apply h1
    have hx : ((x.val : ℕ) : ZMod n) = x := ZMod.natCast_zmod_val x
    rw [hc] at hx; simpa using hx.symm
  omega

/-- **The forward-arc sub-polygon** of a diagonal `(i, j)`: vertices `vᵢ, vᵢ₊₁, …, vⱼ`,
indexed by `ZMod ((j - i).val + 1)` via `k ↦ vᵢ₊ₖ`. The closing edge (`vⱼ → vᵢ`) is the
diagonal. -/
def splitPoly (P : LatticePolygon) (i j : ZMod P.n) : LatticePolygon where
  n := (j - i).val + 1
  pos := Nat.succ_pos _
  vert := fun k => P.vert (i + (k.val : ZMod P.n))

@[simp] lemma splitPoly_n (P : LatticePolygon) (i j : ZMod P.n) :
    (splitPoly P i j).n = (j - i).val + 1 := rfl

@[simp] lemma splitPoly_vert (P : LatticePolygon) (i j : ZMod P.n)
    (k : ZMod (splitPoly P i j).n) :
    (splitPoly P i j).vert k = P.vert (i + ((k.val : ZMod P.n))) := rfl

/-- Each arc has **at least `3`** vertices when the diagonal is non-adjacent
(`i ≠ j`, `i + 1 ≠ j`). -/
lemma three_le_splitPoly_n (P : LatticePolygon) (h2 : 2 ≤ P.n) (i j : ZMod P.n)
    (hij : i ≠ j) (hij1 : i + 1 ≠ j) : 3 ≤ (splitPoly P i j).n := by
  simp only [splitPoly_n]
  have hx0 : j - i ≠ 0 := sub_ne_zero.2 (Ne.symm hij)
  have hx1 : j - i ≠ 1 := by
    intro hc; apply hij1; rw [← hc]; ring
  have := two_le_val P.n h2 (j - i) hx0 hx1
  omega

/-- Each arc has **strictly fewer** than `P.n` vertices when the diagonal is non-adjacent on
the other side (`j + 1 ≠ i`). -/
lemma splitPoly_n_lt (P : LatticePolygon) (h2 : 2 ≤ P.n) (i j : ZMod P.n)
    (hij : i ≠ j) (hji1 : j + 1 ≠ i) : (splitPoly P i j).n < P.n := by
  simp only [splitPoly_n]
  -- `(j - i).val + 1 < n  ⟺  (j - i).val < n - 1  ⟺  j - i ≠ -1`, i.e. `j ≠ i - 1`.
  have hx0 : -(j - i) ≠ 0 := by
    rw [neg_ne_zero]; exact sub_ne_zero.2 (Ne.symm hij)
  have hx1 : -(j - i) ≠ 1 := by
    intro hc
    apply hji1
    have h' : j - i = -1 := by rw [← neg_neg (j - i), hc]
    linear_combination h'
  have hsum : (j - i).val + (-(j - i)).val = P.n := val_add_val_neg P.n (j - i) (sub_ne_zero.2 (Ne.symm hij))
  have hge2 : 2 ≤ (-(j - i)).val := two_le_val P.n h2 (-(j - i)) hx0 hx1
  omega

/-! ### Polygon split across a diagonal: edge reindexing and the mechanical `IsSimple` clauses

The edges of `splitPoly P i j` reindex onto `P`'s edges exactly like the ear clip: a
**kept edge** for `k.val < (j - i).val` (`edgeSeg k = P.edgeSeg (i + k.val)`), and the
**diagonal edge** for `k.val = (j - i).val` (`edgeSeg k = [v_j, v_i]`). We record the
reindexing arithmetic and the *mechanical* `IsSimple` obligations that inherit directly
from `P` (nondegeneracy of kept edges, kept–kept disjointness). The remaining geometric
clauses (diagonal–edge disjointness and the adjacent-meeting clause) need `IsDiagonal`,
deferred. Mirrors `deleteLast_*` in `Pick.EarClip`. -/

/-- A **kept edge** of the split: for `k.val < (j - i).val`, edge `k` of `splitPoly P i j`
coincides with edge `↑(i + k.val)` of `P`. -/
lemma splitPoly_edgeSeg_kept (P : LatticePolygon) (i j : ZMod P.n)
    (k : ZMod (splitPoly P i j).n) (hk : k.val < (j - i).val) :
    (splitPoly P i j).edgeSeg k = P.edgeSeg (i + ((k.val : ℕ) : ZMod P.n)) := by
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  have hcast : (k + 1) = ((k.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have hsucc : ((k + 1).val : ℕ) = k.val + 1 := by
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hidx : i + (((k + 1).val : ℕ) : ZMod P.n) = (i + ((k.val : ℕ) : ZMod P.n)) + 1 := by
    rw [hsucc]; push_cast; ring
  rw [LatticePolygon.edgeSeg, LatticePolygon.edgeSeg, splitPoly_vert, splitPoly_vert, hidx]

/-- The **diagonal edge** of the split: the last edge `k.val = (j - i).val` of
`splitPoly P i j` is the diagonal segment `v_j → v_i`. -/
lemma splitPoly_edgeSeg_diag (P : LatticePolygon) (i j : ZMod P.n)
    (k : ZMod (splitPoly P i j).n) (hk : k.val = (j - i).val) :
    (splitPoly P i j).edgeSeg k = segment ℝ (toReal (P.vert j)) (toReal (P.vert i)) := by
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  have hcast : (k + 1) = ((k.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have hz : (k + 1) = 0 := by
    rw [hcast, hk, show ((j - i).val + 1 : ℕ) = (splitPoly P i j).n from hN.symm]
    exact_mod_cast ZMod.natCast_self _
  have hzval : ((k + 1).val : ℕ) = 0 := by rw [hz, ZMod.val_zero]
  have hvk : i + ((k.val : ℕ) : ZMod P.n) = j := by rw [hk, ZMod.natCast_zmod_val]; ring
  have hvk1 : i + (((k + 1).val : ℕ) : ZMod P.n) = i := by rw [hzval]; simp
  rw [LatticePolygon.edgeSeg, splitPoly_vert, splitPoly_vert, hvk, hvk1]

/-- Every split index `k` is either a kept edge (`k.val < (j - i).val`) or the diagonal
(`k.val = (j - i).val`). -/
lemma splitPoly_idx_dichotomy (P : LatticePolygon) (i j : ZMod P.n)
    (k : ZMod (splitPoly P i j).n) : k.val < (j - i).val ∨ k.val = (j - i).val := by
  have hlt := ZMod.val_lt k
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  omega

/-- The `P`-index of a kept edge's successor: `↑(k+1).val = ↑k.val + 1` in `ZMod P.n`. -/
lemma splitPoly_idx_succ (P : LatticePolygon) (i j : ZMod P.n)
    (k : ZMod (splitPoly P i j).n) (hk : k.val < (j - i).val) :
    ((((k + 1).val) : ℕ) : ZMod P.n) = ((k.val : ℕ) : ZMod P.n) + 1 := by
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  have hcast : (k + 1) = ((k.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have hsucc : ((k + 1).val : ℕ) = k.val + 1 := by
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [hsucc]; push_cast; ring

/-- The `P`-index map `k ↦ ↑k.val : ZMod ((j-i).val+1) → ZMod P.n` is injective (both
vals are `< (j-i).val+1 ≤ P.n`). -/
lemma splitPoly_idx_inj (P : LatticePolygon) (i j : ZMod P.n)
    (a b : ZMod (splitPoly P i j).n)
    (he : ((a.val : ℕ) : ZMod P.n) = ((b.val : ℕ) : ZMod P.n)) : a = b := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  have hji := ZMod.val_lt (j - i)
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
  exact ZMod.val_injective _ he

/-- **Clause 1 for the split: no degenerate edge.** Kept edges inherit `P`'s
nondegeneracy; the diagonal `v_j → v_i` is nondegenerate because `i ≠ j` and the vertex
map is injective. -/
lemma splitPoly_nondegenerate (P : LatticePolygon) (hS : P.IsSimple) (i j : ZMod P.n)
    (hij : i ≠ j) :
    ∀ k, (splitPoly P i j).vert k ≠ (splitPoly P i j).vert (k + 1) := by
  intro k
  rcases splitPoly_idx_dichotomy P i j k with hlt | heq
  · rw [splitPoly_vert, splitPoly_vert]
    intro he
    have hidx : i + ((((k + 1).val) : ℕ) : ZMod P.n) = (i + ((k.val : ℕ) : ZMod P.n)) + 1 := by
      rw [splitPoly_idx_succ P i j k hlt]; ring
    exact hS.1 (i + ((k.val : ℕ) : ZMod P.n)) (by rw [← hidx]; exact he)
  · rw [splitPoly_vert, splitPoly_vert]
    have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
    have hcast : (k + 1) = ((k.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    have hz : (k + 1) = 0 := by
      rw [hcast, heq, show ((j - i).val + 1 : ℕ) = (splitPoly P i j).n from hN.symm]
      exact_mod_cast ZMod.natCast_self _
    have hzval : ((k + 1).val : ℕ) = 0 := by rw [hz, ZMod.val_zero]
    have hvk : i + ((k.val : ℕ) : ZMod P.n) = j := by rw [heq, ZMod.natCast_zmod_val]; ring
    have hvk1 : i + (((k + 1).val : ℕ) : ZMod P.n) = i := by rw [hzval]; simp
    rw [hvk, hvk1]
    exact fun he => hij (vert_injective P hS he).symm

/-- **Clause 2 for the split, kept–kept case.** Two distinct, non-adjacent kept edges of
`splitPoly P i j` are disjoint, inherited from `P`'s simplicity. -/
lemma splitPoly_kept_disjoint (P : LatticePolygon) (hS : P.IsSimple) (i j : ZMod P.n)
    (a b : ZMod (splitPoly P i j).n) (ha : a.val < (j - i).val) (hb : b.val < (j - i).val)
    (hne : a ≠ b) (hadj1 : a + 1 ≠ b) (hadj2 : b + 1 ≠ a) :
    Disjoint (P.edgeSeg (i + ((a.val : ℕ) : ZMod P.n)))
      (P.edgeSeg (i + ((b.val : ℕ) : ZMod P.n))) := by
  apply hS.2.1
  · exact fun he => hne (splitPoly_idx_inj P i j a b (add_left_cancel he))
  · intro he
    have h2 : i + ((((a + 1).val) : ℕ) : ZMod P.n) = i + ((b.val : ℕ) : ZMod P.n) := by
      rw [splitPoly_idx_succ P i j a ha, ← he]; ring
    exact hadj1 (splitPoly_idx_inj P i j (a + 1) b (add_left_cancel h2))
  · intro he
    have h2 : i + ((((b + 1).val) : ℕ) : ZMod P.n) = i + ((a.val : ℕ) : ZMod P.n) := by
      rw [splitPoly_idx_succ P i j b hb, ← he]; ring
    exact hadj2 (splitPoly_idx_inj P i j (b + 1) a (add_left_cancel h2))

/-- **The forward-arc sub-polygon of a diagonal is simple.** Given `IsDiagonal P i j`, the
arc `vᵢ, …, vⱼ` closed by the diagonal edge `vⱼ → vᵢ` is a simple polygon. Clause 1
(nondegeneracy) is `splitPoly_nondegenerate`; clause 2 (non-adjacent disjointness) splits into
kept–kept (`splitPoly_kept_disjoint`) and kept–diagonal cases, the latter from the diagonal's
edge-disjointness (the closed diagonal meets a non-incident kept edge nowhere: open part by
`IsDiagonal`, endpoints by `vert_notMem_edgeSeg`); clause 3 (adjacent edges meet at the shared
vertex) inherits from `P` for kept–kept, and at the two diagonal endpoints reduces to the same
`IsDiagonal`/`vert_notMem_edgeSeg` facts. -/
lemma splitPoly_isSimple_of_diagonal (P : LatticePolygon) (hS : P.IsSimple) (h2 : 2 ≤ P.n)
    (i j : ZMod P.n) (hdiag : IsDiagonal P i j) :
    (splitPoly P i j).IsSimple := by
  classical
  obtain ⟨hij, hij1, hji1, hdisj⟩ := hdiag
  set vi := toReal (P.vert i) with hvidef
  set vj := toReal (P.vert j) with hvjdef
  have hdlt : (j - i).val < P.n := ZMod.val_lt _
  have hd2 : 2 ≤ (j - i).val := by
    have h := three_le_splitPoly_n P h2 i j hij hij1; simp only [splitPoly_n] at h; omega
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  -- nat-cast injectivity below `P.n`
  have hcastne : ∀ x y : ℕ, x < P.n → y < P.n → x ≠ y →
      ((x : ℕ) : ZMod P.n) ≠ ((y : ℕ) : ZMod P.n) := by
    intro x y hx hy hxy hc
    apply hxy
    have h := congrArg ZMod.val hc
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  have idxne : ∀ (x y : ℕ), x < P.n → y < P.n → x ≠ y →
      i + ((x : ℕ) : ZMod P.n) ≠ i + ((y : ℕ) : ZMod P.n) :=
    fun x y hx hy hxy h => (hcastne x y hx hy hxy) (add_left_cancel h)
  -- index landmarks: `j = i + (j-i).val`, `j - 1 = i + ((j-i).val - 1)`, `i - 1 = i + (n-1)`
  have hjeq : j = i + (((j - i).val : ℕ) : ZMod P.n) := by rw [ZMod.natCast_zmod_val]; ring
  have hj1eq : j - 1 = i + ((((j - i).val - 1) : ℕ) : ZMod P.n) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_zmod_val]; ring
  have hm1 : ((P.n - 1 : ℕ) : ZMod P.n) = -1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self]; ring
  -- closed diagonal disjoint from a `P`-edge avoiding both endpoints
  have hdiagClosed : ∀ e : ZMod P.n, vi ∉ P.edgeSeg e → vj ∉ P.edgeSeg e →
      Disjoint (segment ℝ vj vi) (P.edgeSeg e) := by
    intro e hvi hvj
    rw [Set.disjoint_left]
    intro p hp hpe
    have hpvj : p ≠ vj := fun h => hvj (h ▸ hpe)
    have hpvi : p ≠ vi := fun h => hvi (h ▸ hpe)
    have hopen : p ∈ openSegment ℝ vj vi := mem_openSegment_of_ne_ends hp hpvj hpvi
    rw [openSegment_symm] at hopen
    exact Set.disjoint_left.mp (hdisj e) hopen hpe
  -- kept index `c` (non-adjacent to the diagonal): closed diagonal disjoint from edge `i + c`
  have keptDiagDisj : ∀ c : ZMod (splitPoly P i j).n, c.val < (j - i).val → c ≠ 0 →
      c.val ≠ (j - i).val - 1 →
      Disjoint (P.edgeSeg (i + ((c.val : ℕ) : ZMod P.n))) (segment ℝ vj vi) := by
    intro c hc hc0 hcd
    have hc1 : 1 ≤ c.val := by
      have : c.val ≠ 0 := fun h => hc0 ((ZMod.val_eq_zero c).mp h); omega
    have hc2 : c.val ≤ (j - i).val - 2 := by omega
    have hvi : vi ∉ P.edgeSeg (i + ((c.val : ℕ) : ZMod P.n)) := by
      apply vert_notMem_edgeSeg P hS i
      · simpa using idxne c.val 0 (by omega) (by omega) (by omega)
      · rw [show (i : ZMod P.n) - 1 = i + ((P.n - 1 : ℕ) : ZMod P.n) by rw [hm1]; ring]
        exact idxne c.val (P.n - 1) (by omega) (by omega) (by omega)
    have hvj : vj ∉ P.edgeSeg (i + ((c.val : ℕ) : ZMod P.n)) := by
      apply vert_notMem_edgeSeg P hS j
      · intro h; exact idxne c.val (j - i).val (by omega) (by omega) (by omega) (h.trans hjeq)
      · intro h
        exact idxne c.val ((j - i).val - 1) (by omega) (by omega) (by omega) (h.trans hj1eq)
    exact (hdiagClosed _ hvi hvj).symm
  refine ⟨splitPoly_nondegenerate P hS i j hij, ?_, ?_⟩
  · -- Clause 2: non-adjacent edges disjoint
    intro a b hne hadj1 hadj2
    rcases splitPoly_idx_dichotomy P i j a with ha | ha <;>
      rcases splitPoly_idx_dichotomy P i j b with hb | hb
    · -- both kept
      rw [splitPoly_edgeSeg_kept P i j a ha, splitPoly_edgeSeg_kept P i j b hb]
      exact splitPoly_kept_disjoint P hS i j a b ha hb hne hadj1 hadj2
    · -- a kept, b diagonal
      rw [splitPoly_edgeSeg_kept P i j a ha, splitPoly_edgeSeg_diag P i j b hb]
      have hb0 : b + 1 = 0 := by
        have hcast : (b + 1) = ((b.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, hb, show ((j - i).val + 1 : ℕ) = (splitPoly P i j).n from rfl]
        exact_mod_cast ZMod.natCast_self _
      have ha0 : a ≠ 0 := fun h => hadj2 (by rw [hb0, h])
      have had : a.val ≠ (j - i).val - 1 := by
        intro hc
        apply hadj1
        have hav : (a + 1).val = (j - i).val := by
          have hcast : (a + 1) = ((a.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
            rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
          rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; omega
        exact ZMod.val_injective _ (hav.trans hb.symm)
      exact keptDiagDisj a ha ha0 had
    · -- a diagonal, b kept
      rw [splitPoly_edgeSeg_diag P i j a ha, splitPoly_edgeSeg_kept P i j b hb]
      have ha0' : a + 1 = 0 := by
        have hcast : (a + 1) = ((a.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, ha, show ((j - i).val + 1 : ℕ) = (splitPoly P i j).n from rfl]
        exact_mod_cast ZMod.natCast_self _
      have hb0 : b ≠ 0 := fun h => hadj1 (by rw [ha0', h])
      have hbd : b.val ≠ (j - i).val - 1 := by
        intro hc
        apply hadj2
        have hbv : (b + 1).val = (j - i).val := by
          have hcast : (b + 1) = ((b.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
            rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
          rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; omega
        exact ZMod.val_injective _ (hbv.trans ha.symm)
      exact (keptDiagDisj b hb hb0 hbd).symm
    · -- both diagonal: same index, impossible
      exact absurd (ZMod.val_injective _ (ha.trans hb.symm)) hne
  · -- Clause 3: adjacent edges meet exactly at the shared vertex
    intro k
    have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
    rcases (show k.val < (j - i).val - 1 ∨ k.val = (j - i).val - 1 ∨ k.val = (j - i).val from by
      have hvl := ZMod.val_lt k; omega) with hlt | hmid | hlast
    · -- both `k` and `k+1` kept
      have hk : k.val < (j - i).val := by omega
      have hsucc : ((k + 1).val : ℕ) = k.val + 1 := by
        have hcast : (k + 1) = ((k.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have hk1 : (k + 1).val < (j - i).val := by rw [hsucc]; omega
      have hes1 : (splitPoly P i j).edgeSeg k = P.edgeSeg (i + ((k.val : ℕ) : ZMod P.n)) :=
        splitPoly_edgeSeg_kept P i j k hk
      have hidx : i + (((k + 1).val : ℕ) : ZMod P.n) = (i + ((k.val : ℕ) : ZMod P.n)) + 1 := by
        rw [splitPoly_idx_succ P i j k hk, add_assoc]
      have hes2 : (splitPoly P i j).edgeSeg (k + 1)
          = P.edgeSeg ((i + ((k.val : ℕ) : ZMod P.n)) + 1) := by
        rw [splitPoly_edgeSeg_kept P i j (k + 1) hk1, hidx]
      have hdv : toReal ((splitPoly P i j).vert (k + 1))
          = toReal (P.vert ((i + ((k.val : ℕ) : ZMod P.n)) + 1)) := by
        rw [splitPoly_vert, hidx]
      rw [hes1, hes2, hdv]
      exact hS.2.2 (i + ((k.val : ℕ) : ZMod P.n))
    · -- `k` kept (val = d-1), `k+1` diagonal (val = d); shared vertex `vⱼ`
      have hk : k.val < (j - i).val := by omega
      have hsucc : ((k + 1).val : ℕ) = (j - i).val := by
        have hcast : (k + 1) = ((k.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; omega
      have hkidx : i + ((k.val : ℕ) : ZMod P.n) = j - 1 := by
        rw [hj1eq, hmid]
      have hes1 : (splitPoly P i j).edgeSeg k = P.edgeSeg (j - 1) := by
        rw [splitPoly_edgeSeg_kept P i j k hk, hkidx]
      have hes2 : (splitPoly P i j).edgeSeg (k + 1) = segment ℝ vj vi :=
        splitPoly_edgeSeg_diag P i j (k + 1) hsucc
      have hdv : toReal ((splitPoly P i j).vert (k + 1)) = vj := by
        rw [splitPoly_vert, hsucc, ← hjeq]
      rw [hes1, hes2, hdv]
      -- `P.edgeSeg (j-1) ∩ segment vj vi = {vj}`
      have hjm1edge : P.edgeSeg (j - 1) = segment ℝ (toReal (P.vert (j - 1))) vj := by
        rw [LatticePolygon.edgeSeg, show (j - 1) + 1 = j by ring]
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨⟨by rw [hjm1edge]; exact right_mem_segment ℝ _ _, left_mem_segment ℝ vj vi⟩, ?_⟩
      rintro p ⟨hp1, hp2⟩
      by_contra hpne
      have hpvi : p ≠ vi := by
        intro h; subst h
        exact vert_notMem_edgeSeg P hS i (j - 1)
          (fun he => hij1 (by linear_combination -he)) (fun he => hij (by linear_combination -he)) hp1
      have hopen : p ∈ openSegment ℝ vj vi := mem_openSegment_of_ne_ends hp2 hpne hpvi
      rw [openSegment_symm] at hopen
      exact Set.disjoint_left.mp (hdisj (j - 1)) hopen hp1
    · -- `k` diagonal (val = d), `k+1 = 0` (edge `[vᵢ, vᵢ₊₁]`); shared vertex `vᵢ`
      have hz : (k + 1) = 0 := by
        have hcast : (k + 1) = ((k.val + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, hlast, show ((j - i).val + 1 : ℕ) = (splitPoly P i j).n from rfl]
        exact_mod_cast ZMod.natCast_self _
      have hzval : ((k + 1).val : ℕ) = 0 := by rw [hz, ZMod.val_zero]
      have hk1 : (k + 1).val < (j - i).val := by rw [hzval]; omega
      have hes1 : (splitPoly P i j).edgeSeg k = segment ℝ vj vi :=
        splitPoly_edgeSeg_diag P i j k hlast
      have hes2 : (splitPoly P i j).edgeSeg (k + 1) = P.edgeSeg i := by
        rw [splitPoly_edgeSeg_kept P i j (k + 1) hk1, hzval]; simp
      have hdv : toReal ((splitPoly P i j).vert (k + 1)) = vi := by
        rw [splitPoly_vert, hzval, Nat.cast_zero, add_zero]
      rw [hes1, hes2, hdv]
      have hiedge : P.edgeSeg i = segment ℝ vi (toReal (P.vert (i + 1))) := by
        rw [LatticePolygon.edgeSeg]
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨⟨right_mem_segment ℝ vj vi, by rw [hiedge]; exact left_mem_segment ℝ _ _⟩, ?_⟩
      rintro p ⟨hp1, hp2⟩
      by_contra hpne
      have hpvj : p ≠ vj := by
        intro h; subst h
        exact vert_notMem_edgeSeg P hS j i hij (fun he => hij1 (by linear_combination he)) hp2
      have hopen : p ∈ openSegment ℝ vj vi := mem_openSegment_of_ne_ends hp1 hpvj hpne
      rw [openSegment_symm] at hopen
      exact Set.disjoint_left.mp (hdisj i) hopen hp2

/-! ### Task 1: shoelace additivity across a diagonal split -/

/-- Sum over `ZMod m` as a sum over `Finset.range m` via the canonical cast. -/
lemma sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (m : ℕ) [NeZero m]
    (G : ZMod m → M) : (∑ k : ZMod m, G k) = ∑ c ∈ Finset.range m, G (c : ZMod m) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by have := NeZero.ne m; omega⟩
  rw [← Fin.sum_univ_eq_sum_range (fun c => G (c : ZMod (p + 1))) (p + 1)]
  refine Fintype.sum_congr _ _ ?_
  intro k
  exact congrArg G (ZMod.natCast_rightInverse k).symm

/-- **Cross-sum of the forward arc.** The cyclic cross-sum (shoelace numerator) of
`splitPoly P i j` equals the sum of `P`'s cross-terms over the kept edges `i, …, j-1`
plus the single diagonal term `cross(vⱼ, vᵢ)`. -/
lemma splitPoly_cross_arc (P : LatticePolygon) (i j : ZMod P.n) :
    (∑ k : ZMod (splitPoly P i j).n,
        cross (toReal ((splitPoly P i j).vert k)) (toReal ((splitPoly P i j).vert (k + 1))))
      = (∑ c ∈ Finset.range (j - i).val,
          cross (toReal (P.vert (i + (c : ZMod P.n)))) (toReal (P.vert (i + (c : ZMod P.n) + 1))))
        + cross (toReal (P.vert j)) (toReal (P.vert i)) := by
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  have hvalc : ∀ c : ℕ, c < (j - i).val + 1 →
      ((c : ZMod (splitPoly P i j).n).val : ℕ) = c := by
    intro c hc
    rw [ZMod.val_natCast, hN, Nat.mod_eq_of_lt hc]
  have hsucc : ∀ c : ℕ, ((c : ZMod (splitPoly P i j).n) + 1)
      = ((c + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
    intro c; push_cast; ring
  have hconv : (∑ k : ZMod (splitPoly P i j).n,
        cross (toReal ((splitPoly P i j).vert k)) (toReal ((splitPoly P i j).vert (k + 1))))
      = ∑ c ∈ Finset.range ((j - i).val + 1),
          cross (toReal ((splitPoly P i j).vert (c : ZMod (splitPoly P i j).n)))
            (toReal ((splitPoly P i j).vert ((c : ZMod (splitPoly P i j).n) + 1))) :=
    sum_zmod_eq_sum_range (splitPoly P i j).n _
  rw [hconv, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    have e1 : (splitPoly P i j).vert (c : ZMod (splitPoly P i j).n)
        = P.vert (i + (c : ZMod P.n)) := by
      rw [splitPoly_vert, hvalc c (by omega)]
    have hsv : ((((c : ZMod (splitPoly P i j).n) + 1).val : ℕ) : ZMod P.n)
        = (c : ZMod P.n) + 1 := by
      rw [hsucc, hvalc (c + 1) (by omega)]; push_cast; ring
    have e2 : (splitPoly P i j).vert ((c : ZMod (splitPoly P i j).n) + 1)
        = P.vert (i + (c : ZMod P.n) + 1) := by
      rw [splitPoly_vert, hsv]; congr 1; ring
    rw [e1, e2]
  · have hjv : ((j - i).val : ZMod P.n) = j - i := ZMod.natCast_zmod_val _
    have e1 : (splitPoly P i j).vert (((j - i).val : ℕ) : ZMod (splitPoly P i j).n)
        = P.vert j := by
      rw [splitPoly_vert, hvalc (j - i).val (Nat.lt_succ_self _), hjv]
      congr 1; ring
    have hz : (((j - i).val : ℕ) : ZMod (splitPoly P i j).n) + 1 = 0 := by
      rw [hsucc]; exact_mod_cast ZMod.natCast_self ((j - i).val + 1)
    have e2 : (splitPoly P i j).vert ((((j - i).val : ℕ) : ZMod (splitPoly P i j).n) + 1)
        = P.vert i := by
      rw [hz, splitPoly_vert, ZMod.val_zero]; simp
    rw [e1, e2]

/-- **Task 1: shoelace additivity across a diagonal split.** The two arc sub-polygons
cover all of `P`'s edges once; the diagonal edge appears once in each orientation, so its
two cross-terms cancel, leaving `P`'s shoelace. -/
lemma splitPoly_shoelace_add (P : LatticePolygon) (i j : ZMod P.n) (hij : i ≠ j) :
    (splitPoly P i j).shoelace + (splitPoly P j i).shoelace = P.shoelace := by
  have hji : j ≠ i := fun h => hij h.symm
  rw [LatticePolygon.shoelace, LatticePolygon.shoelace, LatticePolygon.shoelace,
    splitPoly_cross_arc P i j, splitPoly_cross_arc P j i]
  -- cancel the diagonal cross-terms
  have hcancel : cross (toReal (P.vert j)) (toReal (P.vert i))
      + cross (toReal (P.vert i)) (toReal (P.vert j)) = 0 := by
    rw [cross_skew (toReal (P.vert i)) (toReal (P.vert j))]; ring
  -- reindex the `j`-arc onto the tail of the `i`-arc range
  have hjarc : (∑ c ∈ Finset.range (i - j).val,
        cross (toReal (P.vert (j + (c : ZMod P.n)))) (toReal (P.vert (j + (c : ZMod P.n) + 1))))
      = ∑ c ∈ Finset.range (i - j).val,
        cross (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n))))
          (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n) + 1))) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hidx : i + (((j - i).val + c : ℕ) : ZMod P.n) = j + (c : ZMod P.n) := by
      push_cast; rw [ZMod.natCast_zmod_val]; ring
    rw [hidx]
  -- the two arcs combine to a full range sum, then to the cyclic edge sum
  have hde : (j - i).val + (i - j).val = P.n := by
    have hsub : (i - j) = -(j - i) := by ring
    rw [hsub]; exact val_add_val_neg P.n (j - i) (sub_ne_zero.mpr hji)
  have hfull : (∑ c ∈ Finset.range (j - i).val,
        cross (toReal (P.vert (i + (c : ZMod P.n)))) (toReal (P.vert (i + (c : ZMod P.n) + 1))))
      + (∑ c ∈ Finset.range (i - j).val,
        cross (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n))))
          (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n) + 1))))
      = ∑ x : ZMod P.n, cross (toReal (P.vert x)) (toReal (P.vert (x + 1))) := by
    rw [← Finset.sum_range_add (fun c => cross (toReal (P.vert (i + (c : ZMod P.n))))
      (toReal (P.vert (i + (c : ZMod P.n) + 1)))) (j - i).val (i - j).val, hde]
    rw [← sum_zmod_eq_sum_range P.n (fun x => cross (toReal (P.vert (i + x)))
      (toReal (P.vert (i + x + 1))))]
    rw [← Equiv.sum_comp (Equiv.addLeft i)
      (fun x => cross (toReal (P.vert x)) (toReal (P.vert (x + 1))))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Equiv.coe_addLeft]
  -- assemble
  rw [hjarc]
  rw [show ∀ (a b : ℝ), (a + cross (toReal (P.vert j)) (toReal (P.vert i))) / 2
      + (b + cross (toReal (P.vert i)) (toReal (P.vert j))) / 2 = (a + b) / 2 from
    fun a b => by rw [← add_div]; rw [show a + cross (toReal (P.vert j)) (toReal (P.vert i))
      + (b + cross (toReal (P.vert i)) (toReal (P.vert j)))
      = (a + b) + (cross (toReal (P.vert j)) (toReal (P.vert i))
        + cross (toReal (P.vert i)) (toReal (P.vert j))) from by ring, hcancel, add_zero]]
  rw [hfull]

/-! ### Task 2 (part C): winding additivity across a diagonal split -/

/-- **Winding of the forward arc.** Mirror of `splitPoly_cross_arc` for the winding number:
the winding of `splitPoly P i j` around `q` is the sum of `P`'s edge-winding contributions
over the kept edges `i, …, j-1` plus the diagonal contribution `edgeWind(vⱼ, vᵢ)`. -/
lemma splitPoly_winding_arc (P : LatticePolygon) (i j : ZMod P.n) (q : ℝ × ℝ) :
    (splitPoly P i j).winding q
      = (∑ c ∈ Finset.range (j - i).val,
          LatticePolygon.edgeWind (toReal (P.vert (i + (c : ZMod P.n))))
            (toReal (P.vert (i + (c : ZMod P.n) + 1))) q)
        + LatticePolygon.edgeWind (toReal (P.vert j)) (toReal (P.vert i)) q := by
  rw [LatticePolygon.winding]
  have hN : (splitPoly P i j).n = (j - i).val + 1 := rfl
  have hvalc : ∀ c : ℕ, c < (j - i).val + 1 →
      ((c : ZMod (splitPoly P i j).n).val : ℕ) = c := by
    intro c hc
    rw [ZMod.val_natCast, hN, Nat.mod_eq_of_lt hc]
  have hsucc : ∀ c : ℕ, ((c : ZMod (splitPoly P i j).n) + 1)
      = ((c + 1 : ℕ) : ZMod (splitPoly P i j).n) := by
    intro c; push_cast; ring
  have hconv : (∑ k : ZMod (splitPoly P i j).n,
        LatticePolygon.edgeWind (toReal ((splitPoly P i j).vert k))
          (toReal ((splitPoly P i j).vert (k + 1))) q)
      = ∑ c ∈ Finset.range ((j - i).val + 1),
          LatticePolygon.edgeWind (toReal ((splitPoly P i j).vert (c : ZMod (splitPoly P i j).n)))
            (toReal ((splitPoly P i j).vert ((c : ZMod (splitPoly P i j).n) + 1))) q :=
    sum_zmod_eq_sum_range (splitPoly P i j).n _
  rw [hconv, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    have e1 : (splitPoly P i j).vert (c : ZMod (splitPoly P i j).n)
        = P.vert (i + (c : ZMod P.n)) := by
      rw [splitPoly_vert, hvalc c (by omega)]
    have hsv : ((((c : ZMod (splitPoly P i j).n) + 1).val : ℕ) : ZMod P.n)
        = (c : ZMod P.n) + 1 := by
      rw [hsucc, hvalc (c + 1) (by omega)]; push_cast; ring
    have e2 : (splitPoly P i j).vert ((c : ZMod (splitPoly P i j).n) + 1)
        = P.vert (i + (c : ZMod P.n) + 1) := by
      rw [splitPoly_vert, hsv]; congr 1; ring
    rw [e1, e2]
  · have hjv : ((j - i).val : ZMod P.n) = j - i := ZMod.natCast_zmod_val _
    have e1 : (splitPoly P i j).vert (((j - i).val : ℕ) : ZMod (splitPoly P i j).n)
        = P.vert j := by
      rw [splitPoly_vert, hvalc (j - i).val (Nat.lt_succ_self _), hjv]; congr 1; ring
    have hz : (((j - i).val : ℕ) : ZMod (splitPoly P i j).n) + 1 = 0 := by
      rw [hsucc]; exact_mod_cast ZMod.natCast_self ((j - i).val + 1)
    have e2 : (splitPoly P i j).vert ((((j - i).val : ℕ) : ZMod (splitPoly P i j).n) + 1)
        = P.vert i := by
      rw [hz, splitPoly_vert, ZMod.val_zero]; simp
    rw [e1, e2]

/-- **Winding additivity across a diagonal split.** For any `q`, the windings of the two
arc sub-polygons sum to `P`'s winding: the two diagonal edge contributions cancel
(`edgeWind_antisymm`), and the kept edges cover `P` once. -/
lemma winding_split_add (P : LatticePolygon) (i j : ZMod P.n) (hij : i ≠ j) (q : ℝ × ℝ) :
    (splitPoly P i j).winding q + (splitPoly P j i).winding q = P.winding q := by
  have hji : j ≠ i := fun h => hij h.symm
  rw [splitPoly_winding_arc P i j q, splitPoly_winding_arc P j i q, LatticePolygon.winding]
  have hcancel : LatticePolygon.edgeWind (toReal (P.vert j)) (toReal (P.vert i)) q
      + LatticePolygon.edgeWind (toReal (P.vert i)) (toReal (P.vert j)) q = 0 :=
    edgeWind_antisymm _ _ _
  have hjarc : (∑ c ∈ Finset.range (i - j).val,
        LatticePolygon.edgeWind (toReal (P.vert (j + (c : ZMod P.n))))
          (toReal (P.vert (j + (c : ZMod P.n) + 1))) q)
      = ∑ c ∈ Finset.range (i - j).val,
        LatticePolygon.edgeWind (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n))))
          (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n) + 1))) q := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hidx : i + (((j - i).val + c : ℕ) : ZMod P.n) = j + (c : ZMod P.n) := by
      push_cast; rw [ZMod.natCast_zmod_val]; ring
    rw [hidx]
  have hde : (j - i).val + (i - j).val = P.n := by
    have hsub : (i - j) = -(j - i) := by ring
    rw [hsub]; exact val_add_val_neg P.n (j - i) (sub_ne_zero.mpr hji)
  have hfull : (∑ c ∈ Finset.range (j - i).val,
        LatticePolygon.edgeWind (toReal (P.vert (i + (c : ZMod P.n))))
          (toReal (P.vert (i + (c : ZMod P.n) + 1))) q)
      + (∑ c ∈ Finset.range (i - j).val,
        LatticePolygon.edgeWind (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n))))
          (toReal (P.vert (i + (((j - i).val + c : ℕ) : ZMod P.n) + 1))) q)
      = ∑ x : ZMod P.n, LatticePolygon.edgeWind (toReal (P.vert x)) (toReal (P.vert (x + 1))) q := by
    rw [← Finset.sum_range_add (fun c => LatticePolygon.edgeWind
      (toReal (P.vert (i + (c : ZMod P.n)))) (toReal (P.vert (i + (c : ZMod P.n) + 1))) q)
      (j - i).val (i - j).val, hde]
    rw [← sum_zmod_eq_sum_range P.n (fun x => LatticePolygon.edgeWind (toReal (P.vert (i + x)))
      (toReal (P.vert (i + x + 1))) q)]
    rw [← Equiv.sum_comp (Equiv.addLeft i)
      (fun x => LatticePolygon.edgeWind (toReal (P.vert x)) (toReal (P.vert (x + 1))) q)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Equiv.coe_addLeft]
  rw [hjarc]
  linarith [hfull, hcancel]

/-- The boundary of an arc sub-polygon `splitPoly P i j` is contained in `P`'s boundary
together with the closed diagonal segment `[v_j, v_i]`: each split edge is either a kept
`P`-edge (`splitPoly_edgeSeg_kept`) or the diagonal (`splitPoly_edgeSeg_diag`). -/
lemma splitPoly_boundary_subset (P : LatticePolygon) (i j : ZMod P.n) :
    (splitPoly P i j).boundary ⊆
      P.boundary ∪ segment ℝ (toReal (P.vert j)) (toReal (P.vert i)) := by
  intro x hx
  rw [LatticePolygon.boundary, Set.mem_iUnion] at hx
  obtain ⟨k, hk⟩ := hx
  rcases splitPoly_idx_dichotomy P i j k with hlt | heq
  · refine Or.inl ?_
    rw [splitPoly_edgeSeg_kept P i j k hlt] at hk
    exact Set.mem_iUnion.mpr ⟨_, hk⟩
  · exact Or.inr (by rwa [splitPoly_edgeSeg_diag P i j k heq] at hk)

/-- **The exterior winding-`0` region reaches infinity (effective exterior connectivity).**
For a simple polygon, any off-boundary point `q` with `winding q = 0` lies in a single
preconnected subset `S ⊆ P.boundaryᶜ` that also contains an arbitrarily-far point (with
winding `0`). This is exactly the package `winding_zero_of_joinedIn_far` consumes, and it
turns "`winding q = 0`" into a concrete far-field witness — the orientation-free version of
"the unbounded component is the exterior". The two-piece decomposition
`compl_boundary_atMost_two` (winding constant on each piece by
`winding_const_of_isPreconnected`) has one winding-`0` piece and one winding-`±1` piece
(`exists_abs_winding_eq_one_of_isSimple` pins the latter `≠ 0`); both `q` and the far point
(`winding_zero_on_cobounded`) land in the winding-`0` piece. -/
lemma exterior_reaches_far (P : LatticePolygon) (hS : P.IsSimple) {q : ℝ × ℝ}
    (hqb : q ∉ P.boundary) (hqw : P.winding q = 0) :
    ∃ S : Set (ℝ × ℝ), S ⊆ P.boundaryᶜ ∧ IsPreconnected S ∧ q ∈ S ∧
      ∃ R : ℝ, (∀ p : ℝ × ℝ, R < ‖p‖ → P.winding p = 0) ∧ ∃ q₀ ∈ S, R < ‖q₀‖ := by
  classical
  obtain ⟨A, B, hAB, hApc, hBpc⟩ := compl_boundary_atMost_two P hS
  have hAsub : A ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_left
  have hBsub : B ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_right
  -- a far point with winding 0
  obtain ⟨Rw, hRw⟩ := winding_zero_on_cobounded P
  have hbd : Bornology.IsBounded P.boundary := by
    unfold LatticePolygon.boundary
    rw [Bornology.isBounded_iUnion]
    intro i
    unfold LatticePolygon.edgeSeg
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isBounded
  obtain ⟨Rb, hRb⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hbd
  set c : ℝ := |Rw| + |Rb| + 1 with hc
  have hcnn : (0 : ℝ) ≤ c := by positivity
  have hcnorm : ‖((c : ℝ), (0 : ℝ))‖ = c := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_zero,
      max_eq_left (abs_nonneg _), abs_of_nonneg hcnn]
  have hcR : Rw < c := by rw [hc]; have := le_abs_self Rw; have := abs_nonneg Rb; linarith
  have hcRb : Rb < c := by rw [hc]; have := le_abs_self Rb; have := abs_nonneg Rw; linarith
  set qf : ℝ × ℝ := (c, 0) with hqf
  have hqfb : qf ∉ P.boundary := by
    intro hmem
    have hmem2 := hRb hmem
    rw [Metric.mem_closedBall, dist_zero_right, hqf, hcnorm] at hmem2
    linarith
  have hqfw : P.winding qf = 0 := hRw qf (by rw [hqf, hcnorm]; exact hcR)
  have hqfnorm : Rw < ‖qf‖ := by rw [hqf, hcnorm]; exact hcR
  -- a winding ≠ 0 point (orientation-free)
  obtain ⟨p1, hp1b, hp1w⟩ := exists_abs_winding_eq_one_of_isSimple P hS
  have hp1ne : P.winding p1 ≠ 0 := by rcases hp1w with h | h <;> rw [h] <;> norm_num
  -- memberships in A ∪ B
  have hqAB : q ∈ A ∪ B := by rw [hAB]; exact hqb
  have hqfAB : qf ∈ A ∪ B := by rw [hAB]; exact hqfb
  have hp1AB : p1 ∈ A ∪ B := by rw [hAB]; exact hp1b
  rcases hp1AB with hp1A | hp1B
  · -- p1 ∈ A, so A is the winding-(≠0) piece; q, qf ∈ B
    refine ⟨B, hBsub, hBpc, ?_, Rw, hRw, qf, ?_, hqfnorm⟩
    · rcases hqAB with hqA | hqB
      · exact absurd ((winding_const_of_isPreconnected P hAsub hApc hp1A hqA).trans hqw) hp1ne
      · exact hqB
    · rcases hqfAB with hqfA | hqfB
      · exact absurd ((winding_const_of_isPreconnected P hAsub hApc hp1A hqfA).trans hqfw) hp1ne
      · exact hqfB
  · -- p1 ∈ B, so B is the winding-(≠0) piece; q, qf ∈ A
    refine ⟨A, hAsub, hApc, ?_, Rw, hRw, qf, ?_, hqfnorm⟩
    · rcases hqAB with hqA | hqB
      · exact hqA
      · exact absurd ((winding_const_of_isPreconnected P hBsub hBpc hp1B hqB).trans hqw) hp1ne
    · rcases hqfAB with hqfA | hqfB
      · exact hqfA
      · exact absurd ((winding_const_of_isPreconnected P hBsub hBpc hp1B hqfB).trans hqfw) hp1ne

/-- **Task 2 reduced to interior disjointness.** Given that the two split sub-polygons'
filled regions `{winding ≠ 0}` are a.e. disjoint, both are positively oriented. The filled
measures add (`winding_split_add` + disjointness), giving
`|L.shoelace| + |R.shoelace| = P.shoelace` (via `abs_shoelace_eq_filledMeasure` and Task 1);
since `L.shoelace + R.shoelace = P.shoelace` too, both shoelaces equal their absolute values,
hence are `≥ 0`, and nonzero (`shoelace_ne_zero_of_isSimple`) forces `> 0`. The disjointness
hypothesis is the remaining Jordan-curve geometric content. -/
lemma splitPoly_positivelyOriented_of_disjoint (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) (i j : ZMod P.n) (hij : i ≠ j)
    (hSL : (splitPoly P i j).IsSimple) (hSR : (splitPoly P j i).IsSimple)
    (hdisj : ∀ᵐ q ∂MeasureTheory.volume,
      ¬((splitPoly P i j).winding q ≠ 0 ∧ (splitPoly P j i).winding q ≠ 0)) :
    (splitPoly P i j).PositivelyOriented ∧ (splitPoly P j i).PositivelyOriented := by
  set L := splitPoly P i j with hLdef
  set R := splitPoly P j i with hRdef
  set AL : Set (ℝ × ℝ) := {q : ℝ × ℝ | L.winding q ≠ 0} with hAL
  set AR : Set (ℝ × ℝ) := {q : ℝ × ℝ | R.winding q ≠ 0} with hAR
  have fL : MeasureTheory.volume AL ≠ ⊤ := windingSupport_volume_ne_top L
  have fR : MeasureTheory.volume AR ≠ ⊤ := windingSupport_volume_ne_top R
  have mAR : MeasurableSet AR := (measurable_winding R (measurableSet_singleton 0)).compl
  -- |shoelace| = filled measure for each piece and for P
  have hLabs : |L.shoelace| = (MeasureTheory.volume AL).toReal :=
    abs_shoelace_eq_filledMeasure L hSL
  have hRabs : |R.shoelace| = (MeasureTheory.volume AR).toReal :=
    abs_shoelace_eq_filledMeasure R hSR
  have hPabs : |P.shoelace| = (MeasureTheory.volume {q : ℝ × ℝ | P.winding q ≠ 0}).toReal :=
    abs_shoelace_eq_filledMeasure P hS
  -- winding additivity (pointwise)
  have hsum : ∀ q, L.winding q + R.winding q = P.winding q := fun q =>
    winding_split_add P i j hij q
  -- the filled region of P agrees a.e. with the union of the pieces' filled regions
  have hUnion : {q : ℝ × ℝ | P.winding q ≠ 0} =ᵐ[MeasureTheory.volume]
      (AL ∪ AR : Set (ℝ × ℝ)) := by
    filter_upwards [hdisj] with q hq
    have hs := hsum q
    have hiff : (q ∈ {q : ℝ × ℝ | P.winding q ≠ 0}) ↔ (q ∈ (AL ∪ AR : Set (ℝ × ℝ))) := by
      simp only [hAL, hAR, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hp
        by_contra hcon
        push Not at hcon
        obtain ⟨hl, hr⟩ := hcon
        omega
      · rintro (hl | hr)
        · have hr0 : R.winding q = 0 := by by_contra h; exact hq ⟨hl, h⟩
          omega
        · have hl0 : L.winding q = 0 := by by_contra h; exact hq ⟨h, hr⟩
          omega
    exact propext hiff
  -- the pieces' filled regions are a.e. disjoint
  have hinter0 : MeasureTheory.volume (AL ∩ AR : Set (ℝ × ℝ)) = 0 := by
    have hbad := MeasureTheory.ae_iff.mp hdisj
    refine MeasureTheory.measure_mono_null ?_ hbad
    intro q hq
    simp only [hAL, hAR, Set.mem_inter_iff, Set.mem_setOf_eq] at hq
    simp only [Set.mem_setOf_eq, not_not]
    exact hq
  -- filled-measure additivity
  have hPvol : MeasureTheory.volume {q : ℝ × ℝ | P.winding q ≠ 0}
      = MeasureTheory.volume AL + MeasureTheory.volume AR := by
    rw [MeasureTheory.measure_congr hUnion,
      MeasureTheory.measure_union₀ mAR.nullMeasurableSet hinter0]
  -- combine to the absolute-value identity
  have hPpos : 0 < P.shoelace := hO
  have hPshoe : P.shoelace = |L.shoelace| + |R.shoelace| := by
    rw [hLabs, hRabs, ← ENNReal.toReal_add fL fR, ← hPvol, ← hPabs, abs_of_pos hPpos]
  have hadd : L.shoelace + R.shoelace = P.shoelace := splitPoly_shoelace_add P i j hij
  -- both shoelaces equal their absolute values, hence ≥ 0, hence > 0
  have hLR : L.shoelace + R.shoelace = |L.shoelace| + |R.shoelace| := by rw [hadd, hPshoe]
  have hLnn : 0 ≤ L.shoelace := by
    linarith [hLR, le_abs_self L.shoelace, le_abs_self R.shoelace, abs_nonneg L.shoelace]
  have hRnn : 0 ≤ R.shoelace := by
    linarith [hLR, le_abs_self L.shoelace, le_abs_self R.shoelace, abs_nonneg R.shoelace]
  have hLne : L.shoelace ≠ 0 := shoelace_ne_zero_of_isSimple L hSL
  have hRne : R.shoelace ≠ 0 := shoelace_ne_zero_of_isSimple R hSR
  exact ⟨lt_of_le_of_ne hLnn (Ne.symm hLne), lt_of_le_of_ne hRnn (Ne.symm hRne)⟩

/-- **Task 1 — the global-witness/sign reduction for `hdisj`.** Given two *separation
witnesses* — a point `pL` in `splitL`'s filled region that is *outside* `splitR`
(`splitR.winding pL = 0`), and the mirror point `pR` inside `splitR` but outside
`splitL` — the a.e.-disjointness of the two filled regions follows by pure
winding/sign algebra, no further geometry.

Each piece, being simple, has a *single global witness value* `v ∈ {±1}` on its filled
set (`winding_mem_zero_or_witness_of_isSimple`). The witness `pL` (off `P.boundary`)
satisfies `P.winding pL = splitL.winding pL = vL` (`winding_split_add`, since
`splitR.winding pL = 0`), and `P.winding pL ∈ {0,1}` (`winding_zero_or_one`), forcing
`vL = 1`; symmetrically `vR = 1`. Then a.e. `q` lies off all three (null) boundaries, and
if both pieces were nonzero there we'd get `P.winding q = vL + vR = 2 ∉ {0,1}`, impossible.

The two witness hypotheses are the *entire* remaining Jordan-curve geometric content
(the diagonal-tube separation: `splitL`'s interior reaches a far-field point off
`splitR.boundary`, mirroring `clip_winding_zero_on_legs`/`winding_one_on_open_ear`). -/
lemma splitPoly_hdisj_of_witnesses (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) (i j : ZMod P.n) (hij : i ≠ j)
    (hSL : (splitPoly P i j).IsSimple) (hSR : (splitPoly P j i).IsSimple)
    (pL : ℝ × ℝ) (hpLL : pL ∉ (splitPoly P i j).boundary) (hpLP : pL ∉ P.boundary)
    (hpLwL : (splitPoly P i j).winding pL ≠ 0) (hpLwR : (splitPoly P j i).winding pL = 0)
    (pR : ℝ × ℝ) (hpRR : pR ∉ (splitPoly P j i).boundary) (hpRP : pR ∉ P.boundary)
    (hpRwR : (splitPoly P j i).winding pR ≠ 0) (hpRwL : (splitPoly P i j).winding pR = 0) :
    ∀ᵐ q ∂MeasureTheory.volume,
      ¬((splitPoly P i j).winding q ≠ 0 ∧ (splitPoly P j i).winding q ≠ 0) := by
  classical
  set L := splitPoly P i j with hLdef
  set R := splitPoly P j i with hRdef
  obtain ⟨vL, hvL01, hLmem⟩ := winding_mem_zero_or_witness_of_isSimple L hSL
  obtain ⟨vR, hvR01, hRmem⟩ := winding_mem_zero_or_witness_of_isSimple R hSR
  -- the left witness forces the global value `vL = 1`
  have hvL1 : vL = 1 := by
    have hLpL : L.winding pL = vL := (hLmem pL hpLL).resolve_left hpLwL
    have hadd := winding_split_add P i j hij pL
    rw [← hLdef, ← hRdef, hpLwR, add_zero, hLpL] at hadd
    rcases winding_zero_or_one P hS hO pL hpLP with h0 | h1
    · rw [h0] at hadd; rcases hvL01 with h | h <;> rw [h] at hadd <;> norm_num at hadd
    · rw [h1] at hadd; exact hadd
  -- the right witness forces the global value `vR = 1`
  have hvR1 : vR = 1 := by
    have hRpR : R.winding pR = vR := (hRmem pR hpRR).resolve_left hpRwR
    have hadd := winding_split_add P i j hij pR
    rw [← hLdef, ← hRdef, hpRwL, zero_add, hRpR] at hadd
    rcases winding_zero_or_one P hS hO pR hpRP with h0 | h1
    · rw [h0] at hadd; rcases hvR01 with h | h <;> rw [h] at hadd <;> norm_num at hadd
    · rw [h1] at hadd; exact hadd
  -- a.e. point is off all three (null) boundaries
  have hbLn : L.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero L hSL
  have hbRn : R.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero R hSR
  have hbPn : P.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero P hS
  filter_upwards [hbLn, hbRn, hbPn] with q hqL hqR hqP
  rintro ⟨hLne, hRne⟩
  have hLv : L.winding q = vL := (hLmem q hqL).resolve_left hLne
  have hRv : R.winding q = vR := (hRmem q hqR).resolve_left hRne
  have hadd := winding_split_add P i j hij q
  rw [← hLdef, ← hRdef, hLv, hRv, hvL1, hvR1] at hadd
  rcases winding_zero_or_one P hS hO q hqP with h0 | h1
  · rw [h0] at hadd; norm_num at hadd
  · rw [h1] at hadd; norm_num at hadd

/-- **Task 2 down to the separation witnesses.** Composing
`splitPoly_hdisj_of_witnesses` (Task 1) with
`splitPoly_positivelyOriented_of_disjoint` (already landed): given the two separation
witnesses, both diagonal sub-polygons are positively oriented. -/
lemma splitPoly_positivelyOriented_of_witnesses (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) (i j : ZMod P.n) (hij : i ≠ j)
    (hSL : (splitPoly P i j).IsSimple) (hSR : (splitPoly P j i).IsSimple)
    (pL : ℝ × ℝ) (hpLL : pL ∉ (splitPoly P i j).boundary) (hpLP : pL ∉ P.boundary)
    (hpLwL : (splitPoly P i j).winding pL ≠ 0) (hpLwR : (splitPoly P j i).winding pL = 0)
    (pR : ℝ × ℝ) (hpRR : pR ∉ (splitPoly P j i).boundary) (hpRP : pR ∉ P.boundary)
    (hpRwR : (splitPoly P j i).winding pR ≠ 0) (hpRwL : (splitPoly P i j).winding pR = 0) :
    (splitPoly P i j).PositivelyOriented ∧ (splitPoly P j i).PositivelyOriented :=
  splitPoly_positivelyOriented_of_disjoint P hS hO i j hij hSL hSR
    (splitPoly_hdisj_of_witnesses P hS hO i j hij hSL hSR
      pL hpLL hpLP hpLwL hpLwR pR hpRR hpRP hpRwR hpRwL)

/-- **Partial winding is locally constant at a point off all-but-one edge.**
For a point `q₀` that lies off every edge except possibly edge `e`, with neither
endpoint of edge `e` at height `q₀.2` and no edge horizontal at height `q₀.2`, the
function `winding − edgeWind_e` is locally constant near `q₀`. (This is the
single-edge "winding-jump" content: across edge `e`, the jump of `winding` equals
the jump of `edgeWind_e`.) The proof is the cancellation bookkeeping of
`winding_eventually_eq`, restricted to the sum over `univ.erase e`; edge `e` is a
"good" edge for the bad/pair accounting (`h1e`, `h2e`), so the full shift identity
still collapses to `0`. -/
lemma winding_sub_edge_eventually_eq (q₀ : ℝ × ℝ) (e : ZMod P.n)
    (hoff : ∀ j, j ≠ e → q₀ ∉ P.edgeSeg j)
    (h1e : (toReal (P.vert e)).2 ≠ q₀.2)
    (h2e : (toReal (P.vert (e + 1))).2 ≠ q₀.2)
    (hnh : ∀ i, ¬ ((toReal (P.vert i)).2 = q₀.2 ∧ (toReal (P.vert (i + 1))).2 = q₀.2)) :
    ∀ᶠ q in nhds q₀, P.winding q - edgeWind (toReal (P.vert e)) (toReal (P.vert (e + 1))) q
      = P.winding q₀ - edgeWind (toReal (P.vert e)) (toReal (P.vert (e + 1))) q₀ := by
  classical
  set H := q₀.2 with hH
  set bad : ZMod P.n → ℤ := fun k => if (toReal (P.vert k)).2 = H then 1 else 0 with hbad
  set f : ZMod P.n → ℝ × ℝ → ℤ :=
    fun i q => edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q with hf
  have hbade : bad e = 0 := by simp only [hbad]; exact if_neg (by rw [hH]; exact h1e)
  have hbade1 : bad (e + 1) = 0 := by simp only [hbad]; exact if_neg (by rw [hH]; exact h2e)
  -- For each vertex `k` at height `H`, its two incident edges cancel near `q₀`.
  have hpair : ∀ k ∈ (Finset.univ : Finset (ZMod P.n)),
      (toReal (P.vert k)).2 = H → ∀ᶠ q in nhds q₀,
        f (k - 1) q + f k q = f (k - 1) q₀ + f k q₀ := by
    intro k _ hk
    have hk1 : k - 1 + 1 = k := by abel
    have hke : k ≠ e := by rintro rfl; exact h1e (by rw [hk, hH])
    have hke1 : k - 1 ≠ e := by
      intro h
      have hk' : k = e + 1 := by rw [← h, sub_add_cancel]
      exact h2e (by rw [← hk', hk, hH])
    have hvne : q₀.1 ≠ (toReal (P.vert k)).1 := by
      intro hxe
      have hq₀v : q₀ = toReal (P.vert k) := Prod.ext hxe (by rw [hk])
      refine hoff (k - 1) hke1 ?_
      rw [hq₀v]
      show toReal (P.vert k) ∈ P.edgeSeg (k - 1)
      rw [LatticePolygon.edgeSeg, hk1]
      exact right_mem_segment ℝ _ _
    have h1 : q₀.2 ≠ (toReal (P.vert (k - 1))).2 := by
      intro h
      exact (hnh (k - 1)) ⟨by rw [hH]; exact h.symm, by rw [hk1]; exact hk⟩
    have h2 : q₀.2 ≠ (toReal (P.vert (k + 1))).2 := by
      intro h
      exact (hnh k) ⟨hk, by rw [hH]; exact h.symm⟩
    have hvk : (toReal (P.vert k)).2 = q₀.2 := by rw [hk]
    have hpe := pairWind_eventually_eq (toReal (P.vert (k - 1))) (toReal (P.vert k))
      (toReal (P.vert (k + 1))) q₀ hvk h1 h2 hvne
    filter_upwards [hpe] with q hq
    simp only [hf, hk1]
    exact hq
  -- For each edge `i ≠ e` with neither endpoint at height `H`, the term is locally constant.
  have hgood : ∀ i, i ≠ e → bad i + bad (i + 1) = 0 → ∀ᶠ q in nhds q₀, f i q = f i q₀ := by
    intro i hie hi0
    have hbi : (toReal (P.vert i)).2 ≠ H := by
      intro h; simp only [hbad, if_pos h] at hi0
      have hb1 : (0:ℤ) ≤ bad (i + 1) := by simp only [hbad]; split_ifs <;> norm_num
      omega
    have hbi1 : (toReal (P.vert (i + 1))).2 ≠ H := by
      intro h; simp only [hbad, if_pos h] at hi0
      have hb0 : (0:ℤ) ≤ bad i := by simp only [hbad]; split_ifs <;> norm_num
      omega
    exact edgeWind_eventually_eq_of_not_mem_seg _ _ _
      (fun hmem => hoff i hie hmem) (Ne.symm hbi) (Ne.symm hbi1)
  have evP : ∀ᶠ q in nhds q₀, ∀ k ∈ (Finset.univ : Finset (ZMod P.n)),
      bad k = 1 → f (k - 1) q + f k q = f (k - 1) q₀ + f k q₀ := by
    refine (Finset.eventually_all (I := (Finset.univ : Finset (ZMod P.n)))).mpr (fun k hk => ?_)
    by_cases hkH : (toReal (P.vert k)).2 = H
    · filter_upwards [hpair k hk hkH] with q hq _; exact hq
    · refine Filter.Eventually.of_forall (fun q hbk => ?_)
      have : bad k = 0 := by simp only [hbad, if_neg hkH]
      rw [this] at hbk; exact absurd hbk (by norm_num)
  have evG : ∀ᶠ q in nhds q₀, ∀ i ∈ (Finset.univ : Finset (ZMod P.n)),
      i ≠ e → bad i + bad (i + 1) = 0 → f i q = f i q₀ := by
    refine (Finset.eventually_all (I := (Finset.univ : Finset (ZMod P.n)))).mpr (fun i hi => ?_)
    by_cases hie : i = e
    · exact Filter.Eventually.of_forall (fun q hie' _ => absurd hie hie')
    · by_cases hi0 : bad i + bad (i + 1) = 0
      · filter_upwards [hgood i hie hi0] with q hq; exact fun _ _ => hq
      · exact Filter.Eventually.of_forall (fun q _ hc => absurd hc hi0)
  filter_upwards [evP, evG] with q hqP hqG
  set D : ZMod P.n → ℤ := fun i => f i q - f i q₀ with hD
  have hbad01 : ∀ i, bad i = 0 ∨ bad i = 1 := by
    intro i; simp only [hbad]; split_ifs <;> simp
  have hterm : ∀ i, i ≠ e → D i = (bad i + bad (i + 1)) * D i := by
    intro i hie
    by_cases hsum1 : bad i + bad (i + 1) = 1
    · rw [hsum1, one_mul]
    · rcases hbad01 i with hi | hi <;> rcases hbad01 (i + 1) with hi1 | hi1
      · have hDi : D i = 0 := by
          show f i q - f i q₀ = 0
          rw [hqG i (Finset.mem_univ i) hie (by rw [hi, hi1]; ring)]; ring
        rw [hDi, hi, hi1]; ring
      · exact absurd (show bad i + bad (i + 1) = 1 by rw [hi, hi1]; ring) hsum1
      · exact absurd (show bad i + bad (i + 1) = 1 by rw [hi, hi1]; ring) hsum1
      · exfalso
        have hbi : (toReal (P.vert i)).2 = H := by
          by_contra hc
          have : bad i = 0 := by simp only [hbad, if_neg hc]
          rw [this] at hi; exact absurd hi (by norm_num)
        have hbi1 : (toReal (P.vert (i + 1))).2 = H := by
          by_contra hc
          have : bad (i + 1) = 0 := by simp only [hbad, if_neg hc]
          rw [this] at hi1; exact absurd hi1 (by norm_num)
        exact hnh i ⟨hbi, hbi1⟩
  have hstep2 : (∑ i, (bad i + bad (i + 1)) * D i) = ∑ k, bad k * (D (k - 1) + D k) := by
    calc ∑ i, (bad i + bad (i + 1)) * D i
        = ∑ i, (bad i * D i + bad (i + 1) * D i) := Finset.sum_congr rfl (fun i _ => by ring)
      _ = (∑ i, bad i * D i) + ∑ i, bad (i + 1) * D i := Finset.sum_add_distrib
      _ = (∑ k, bad k * D k) + ∑ k, bad k * D (k - 1) := by
          congr 1
          rw [← Equiv.sum_comp (Equiv.subRight (1 : ZMod P.n))]
          simp [Equiv.subRight]
      _ = ∑ k, bad k * (D (k - 1) + D k) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
  have hzero : ∀ k ∈ (Finset.univ : Finset (ZMod P.n)), bad k * (D (k - 1) + D k) = 0 := by
    intro k _
    rcases hbad01 k with hk0 | hk1
    · rw [hk0]; ring
    · have hpk := hqP k (Finset.mem_univ k) hk1
      have : D (k - 1) + D k = 0 := by rw [hD]; simp only; linarith [hpk]
      rw [this]; ring
  have htgt : ∑ i ∈ Finset.univ.erase e, D i = 0 := by
    have hcong : ∑ i ∈ Finset.univ.erase e, D i
        = ∑ i ∈ Finset.univ.erase e, (bad i + bad (i + 1)) * D i :=
      Finset.sum_congr rfl (fun i hi => hterm i (Finset.ne_of_mem_erase hi))
    have hee : (bad e + bad (e + 1)) * D e = 0 := by rw [hbade, hbade1]; ring
    have hfull : ∑ i ∈ Finset.univ.erase e, (bad i + bad (i + 1)) * D i
        = ∑ i, (bad i + bad (i + 1)) * D i := by
      rw [← Finset.sum_erase_add Finset.univ
        (fun i => (bad i + bad (i + 1)) * D i) (Finset.mem_univ e), hee, add_zero]
    rw [hcong, hfull, hstep2, Finset.sum_eq_zero hzero]
  show P.winding q - f e q = P.winding q₀ - f e q₀
  have key : ∀ r : ℝ × ℝ, P.winding r = (∑ i ∈ Finset.univ.erase e, f i r) + f e r := by
    intro r
    rw [show P.winding r = ∑ i, f i r from rfl,
      ← Finset.sum_erase_add Finset.univ (fun i => f i r) (Finset.mem_univ e)]
  rw [key q, key q₀]
  have hsplit : (∑ i ∈ Finset.univ.erase e, f i q) = ∑ i ∈ Finset.univ.erase e, f i q₀ := by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]; exact htgt
  linarith [hsplit]

/-- **Partial winding is locally constant at a point off all-but-one edge (no
height restriction).** The horizontal-run-tolerant version of
`winding_sub_edge_eventually_eq`: dropping `hnh`, since horizontal runs at height
`q₀.2` that avoid edge `e` cancel in transition pairs (`pairWind_run_eventually_eq`,
same-side via `same_side_chain`), exactly as in `winding_eventually_eq_full`. Edge
`e` is a fixed point of the matching involution (`h1e`, `h2e` ⇒ neither endpoint at
height `q₀.2`), so the involution restricts to `univ.erase e` and the partial sum
collapses to `0`. -/
lemma winding_sub_edge_eventually_eq_full (q₀ : ℝ × ℝ) (e : ZMod P.n)
    (hoff : ∀ j, j ≠ e → q₀ ∉ P.edgeSeg j)
    (h1e : (toReal (P.vert e)).2 ≠ q₀.2)
    (h2e : (toReal (P.vert (e + 1))).2 ≠ q₀.2) :
    ∀ᶠ q in nhds q₀, P.winding q - edgeWind (toReal (P.vert e)) (toReal (P.vert (e + 1))) q
      = P.winding q₀ - edgeWind (toReal (P.vert e)) (toReal (P.vert (e + 1))) q₀ := by
  classical
  set H := q₀.2 with hH
  set bad : ZMod P.n → Prop := fun k => (toReal (P.vert k)).2 = H with hbad
  have hnbe : ¬ bad e := fun h => h1e (by rw [hH]; exact h)
  have hnbe1 : ¬ bad (e + 1) := fun h => h2e (by rw [hH]; exact h)
  have hsegq : ∀ i, i ≠ e → q₀ ∉ segment ℝ (toReal (P.vert i)) (toReal (P.vert (i + 1))) :=
    fun i hi => hoff i hi
  have hsegqb : ∀ i, bad i → q₀ ∉ segment ℝ (toReal (P.vert i)) (toReal (P.vert (i + 1))) := by
    intro i hi
    exact hsegq i (fun h => hnbe (h ▸ hi))
  have hxne : ∀ k, bad k → q₀.1 ≠ (toReal (P.vert k)).1 := by
    intro k hk hxe
    have hq₀v : q₀ = toReal (P.vert k) := Prod.ext hxe (by rw [hk])
    have hkne : k - 1 ≠ e := by
      intro h
      have hk' : k = e + 1 := by rw [← h, sub_add_cancel]
      apply h2e; rw [← hk', hk]
    refine hsegq (k - 1) hkne ?_
    rw [hq₀v]
    show toReal (P.vert k) ∈ segment ℝ (toReal (P.vert (k - 1))) (toReal (P.vert (k - 1 + 1)))
    rw [sub_add_cancel]; exact right_mem_segment ℝ _ _
  obtain ⟨k₀, hk₀⟩ : ∃ k, ¬ bad k := ⟨e, hnbe⟩
  have hexF : ∀ j : ZMod P.n, ∃ m : ℕ, ¬ bad (j + (m : ZMod P.n)) := by
    intro j
    refine ⟨(k₀ - j).val, ?_⟩
    rw [ZMod.natCast_val, ZMod.cast_id]; simpa using hk₀
  have hexB : ∀ j : ZMod P.n, ∃ s : ℕ, ¬ bad (j - (s : ZMod P.n)) := by
    intro j
    refine ⟨(j - k₀).val, ?_⟩
    rw [ZMod.natCast_val, ZMod.cast_id]; simpa using hk₀
  set fwd : ZMod P.n → ℕ := fun j => Nat.find (hexF j) with hfwd
  set bwd : ZMod P.n → ℕ := fun j => Nat.find (hexB j) with hbwd
  have hfwd_spec : ∀ j, ¬ bad (j + ((fwd j : ℕ) : ZMod P.n)) := fun j => Nat.find_spec (hexF j)
  have hfwd_min : ∀ j, ∀ k : ℕ, k < fwd j → bad (j + (k : ZMod P.n)) := by
    intro j k hk; by_contra hc; exact Nat.find_min (hexF j) hk hc
  have hbwd_spec : ∀ j, ¬ bad (j - ((bwd j : ℕ) : ZMod P.n)) := fun j => Nat.find_spec (hexB j)
  have hbwd_min : ∀ j, ∀ k : ℕ, k < bwd j → bad (j - (k : ZMod P.n)) := by
    intro j k hk; by_contra hc; exact Nat.find_min (hexB j) hk hc
  set f : ZMod P.n → ℝ × ℝ → ℤ :=
    fun i q => edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q with hf
  set tFwd : ZMod P.n → Prop := fun i => ¬ bad i ∧ bad (i + 1) with htFwd
  set tBwd : ZMod P.n → Prop := fun i => bad i ∧ ¬ bad (i + 1) with htBwd
  set g : ZMod P.n → ZMod P.n := fun i =>
    if tFwd i then i + ((fwd (i + 1) : ℕ) : ZMod P.n)
    else if tBwd i then i - ((bwd i : ℕ) : ZMod P.n)
    else i with hg
  have hpair : ∀ᶠ q in nhds q₀, ∀ i ∈ Finset.univ.erase e,
      f i q + f (g i) q = f i q₀ + f (g i) q₀ := by
    refine (Finset.eventually_all (I := Finset.univ.erase e)).mpr (fun i hi => ?_)
    have hie : i ≠ e := Finset.ne_of_mem_erase hi
    by_cases hTF : tFwd i
    · have hbi : ¬ bad i := hTF.1
      have hbi1 : bad (i + 1) := hTF.2
      have hgi : g i = i + ((fwd (i + 1) : ℕ) : ZMod P.n) := by rw [hg]; simp only [if_pos hTF]
      set F := fwd (i + 1) with hF
      have hF1 : 1 ≤ F := by
        rw [Nat.one_le_iff_ne_zero]; intro h
        have hs := hfwd_spec (i + 1); rw [← hF, h] at hs
        simp only [Nat.cast_zero, add_zero] at hs; exact hs hbi1
      have hlast_bad : bad (i + (F : ZMod P.n)) := by
        have hb := hfwd_min (i + 1) (F - 1) (by omega)
        have he : (i + 1) + (((F - 1 : ℕ)) : ZMod P.n) = i + (F : ZMod P.n) := by
          rw [Nat.cast_sub hF1]; push_cast; ring
        rwa [he] at hb
      have hnext_nbad : ¬ bad (i + (F : ZMod P.n) + 1) := by
        have hs := hfwd_spec (i + 1)
        have he : (i + 1) + ((F : ℕ) : ZMod P.n) = i + (F : ZMod P.n) + 1 := by ring
        rw [← hF, he] at hs; exact hs
      have hsame : (q₀.1 < (toReal (P.vert (i + 1))).1 ↔
          q₀.1 < (toReal (P.vert (i + (F : ZMod P.n)))).1) := by
        have hchain := same_side_chain P q₀ (i + 1) H hH.symm (F - 1)
          (fun k hk => hfwd_min (i + 1) k (by omega))
          (fun k hk => hsegqb (i + 1 + (k : ZMod P.n)) (hfwd_min (i + 1) k (by omega)))
        have he : (i + 1) + (((F - 1 : ℕ)) : ZMod P.n) = i + (F : ZMod P.n) := by
          rw [Nat.cast_sub hF1]; push_cast; ring
        rwa [he] at hchain
      have hpe := pairWind_run_eventually_eq (toReal (P.vert i)) (toReal (P.vert (i + 1)))
        (toReal (P.vert (i + (F : ZMod P.n)))) (toReal (P.vert (i + (F : ZMod P.n) + 1))) q₀
        hbi1 hlast_bad (fun h => hbi h.symm) (fun h => hnext_nbad h.symm)
        (hxne (i + 1) hbi1) (hxne (i + (F : ZMod P.n)) hlast_bad) hsame
      filter_upwards [hpe] with q hq
      rw [hgi, hf]; exact hq
    · by_cases hTB : tBwd i
      · have hbi : bad i := hTB.1
        have hbi1 : ¬ bad (i + 1) := hTB.2
        have hgi : g i = i - ((bwd i : ℕ) : ZMod P.n) := by
          rw [hg]; simp only [if_neg hTF, if_pos hTB]
        set B := bwd i with hB
        have hB1 : 1 ≤ B := by
          rw [Nat.one_le_iff_ne_zero]; intro h
          have hs := hbwd_spec i; rw [← hB, h] at hs
          simp only [Nat.cast_zero, sub_zero] at hs; exact hs hbi
        have hentry_nbad : ¬ bad (i - (B : ZMod P.n)) := hbwd_spec i
        have hentry_bad1 : bad (i - (B : ZMod P.n) + 1) := by
          have hb := hbwd_min i (B - 1) (by omega)
          have he : i - ((B - 1 : ℕ) : ZMod P.n) = i - (B : ZMod P.n) + 1 := by
            rw [Nat.cast_sub hB1]; push_cast; ring
          rwa [he] at hb
        have hsame : (q₀.1 < (toReal (P.vert (i - (B : ZMod P.n) + 1))).1 ↔
            q₀.1 < (toReal (P.vert i)).1) := by
          have hchain := same_side_chain P q₀ (i - (B : ZMod P.n) + 1) H hH.symm (B - 1)
            (fun k hk => by
              have hbadk := hbwd_min i (B - 1 - k) (by omega)
              have he : (i - (B : ZMod P.n) + 1) + (k : ZMod P.n)
                  = i - ((B - 1 - k : ℕ) : ZMod P.n) := by
                rw [Nat.cast_sub (by omega), Nat.cast_sub hB1]; push_cast; ring
              rw [he]; exact hbadk)
            (fun k hk => hsegqb (i - (B : ZMod P.n) + 1 + (k : ZMod P.n)) (by
              have hbadk := hbwd_min i (B - 1 - k) (by omega)
              have he : (i - (B : ZMod P.n) + 1) + (k : ZMod P.n)
                  = i - ((B - 1 - k : ℕ) : ZMod P.n) := by
                rw [Nat.cast_sub (by omega), Nat.cast_sub hB1]; push_cast; ring
              rw [he]; exact hbadk))
          have he : (i - (B : ZMod P.n) + 1) + (((B - 1 : ℕ)) : ZMod P.n) = i := by
            rw [Nat.cast_sub hB1]; push_cast; ring
          rwa [he] at hchain
        have hpe := pairWind_run_eventually_eq (toReal (P.vert (i - (B : ZMod P.n))))
          (toReal (P.vert (i - (B : ZMod P.n) + 1))) (toReal (P.vert i))
          (toReal (P.vert (i + 1))) q₀
          hentry_bad1 hbi (fun h => hentry_nbad h.symm) (fun h => hbi1 h.symm)
          (hxne _ hentry_bad1) (hxne i hbi) hsame
        filter_upwards [hpe] with q hq
        have hgf : f (g i) q = edgeWind (toReal (P.vert (i - (B : ZMod P.n))))
            (toReal (P.vert (i - (B : ZMod P.n) + 1))) q := by
          rw [hgi, hf]
        have hgf₀ : f (g i) q₀ = edgeWind (toReal (P.vert (i - (B : ZMod P.n))))
            (toReal (P.vert (i - (B : ZMod P.n) + 1))) q₀ := by
          rw [hgi, hf]
        rw [hgf, hgf₀, hf]; simp only; linarith [hq]
      · have hgi : g i = i := by rw [hg]; simp only [if_neg hTF, if_neg hTB]
        rw [hgi]
        by_cases hbi : bad i
        · have hbi1 : bad (i + 1) := by
            by_contra hc; exact hTB ⟨hbi, hc⟩
          filter_upwards with q
          rw [hf]; simp only
          rw [edgeWind_eq_zero_of_eq_height _ _ q (by rw [hbi, hbi1]),
            edgeWind_eq_zero_of_eq_height _ _ q₀ (by rw [hbi, hbi1])]
        · have hbi1 : ¬ bad (i + 1) := by
            by_contra hc; exact hTF ⟨hbi, hc⟩
          have hev := edgeWind_eventually_eq_of_not_mem_seg
            (toReal (P.vert i)) (toReal (P.vert (i + 1))) q₀ (hsegq i hie)
            (fun h => hbi (by rw [hbad]; exact h.symm))
            (fun h => hbi1 (by rw [hbad]; exact h.symm))
          filter_upwards [hev] with q hq
          rw [hf]; simp only; rw [hq]
  have hinv : ∀ a : ZMod P.n, g (g a) = a := by
    intro a
    by_cases hTF : tFwd a
    · have hbi : ¬ bad a := hTF.1
      have hbi1 : bad (a + 1) := hTF.2
      set F := fwd (a + 1) with hFdef
      have hga : g a = a + (F : ZMod P.n) := by rw [hg]; simp only [if_pos hTF, ← hFdef]
      have hF1 : 1 ≤ F := by
        rw [Nat.one_le_iff_ne_zero]; intro h
        have hs := hfwd_spec (a + 1); rw [← hFdef, h] at hs
        simp only [Nat.cast_zero, add_zero] at hs; exact hs hbi1
      have hlast_bad : bad (a + (F : ZMod P.n)) := by
        have hb := hfwd_min (a + 1) (F - 1) (by omega)
        have he : (a + 1) + (((F - 1 : ℕ)) : ZMod P.n) = a + (F : ZMod P.n) := by
          rw [Nat.cast_sub hF1]; push_cast; ring
        rwa [he] at hb
      have hnext_nbad : ¬ bad (a + (F : ZMod P.n) + 1) := by
        have hs := hfwd_spec (a + 1)
        have he : (a + 1) + ((F : ℕ) : ZMod P.n) = a + (F : ZMod P.n) + 1 := by ring
        rw [← hFdef, he] at hs; exact hs
      have hTFga : ¬ tFwd (a + (F : ZMod P.n)) := fun h => hnext_nbad h.2
      have hTBga : tBwd (a + (F : ZMod P.n)) := ⟨hlast_bad, hnext_nbad⟩
      have hbwdF : bwd (a + (F : ZMod P.n)) = F := by
        rw [hbwd, Nat.find_eq_iff]
        refine ⟨?_, ?_⟩
        · have he : a + (F : ZMod P.n) - (F : ZMod P.n) = a := by ring
          rw [he]; exact hbi
        · intro s hs hns
          have hb := hfwd_min (a + 1) (F - 1 - s) (by omega)
          have he : (a + 1) + ((F - 1 - s : ℕ) : ZMod P.n) = a + (F : ZMod P.n) - (s : ZMod P.n) := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub hF1]; push_cast; ring
          rw [he] at hb; exact hns hb
      rw [hga, hg]; simp only [if_neg hTFga, if_pos hTBga, hbwdF]; ring
    · by_cases hTB : tBwd a
      · have hbi : bad a := hTB.1
        have hbi1 : ¬ bad (a + 1) := hTB.2
        set B := bwd a with hBdef
        have hga : g a = a - (B : ZMod P.n) := by
          rw [hg]; simp only [if_neg hTF, if_pos hTB, ← hBdef]
        have hB1 : 1 ≤ B := by
          rw [Nat.one_le_iff_ne_zero]; intro h
          have hs := hbwd_spec a; rw [← hBdef, h] at hs
          simp only [Nat.cast_zero, sub_zero] at hs; exact hs hbi
        have hentry_nbad : ¬ bad (a - (B : ZMod P.n)) := hbwd_spec a
        have hentry_bad1 : bad (a - (B : ZMod P.n) + 1) := by
          have hb := hbwd_min a (B - 1) (by omega)
          have he : a - ((B - 1 : ℕ) : ZMod P.n) = a - (B : ZMod P.n) + 1 := by
            rw [Nat.cast_sub hB1]; push_cast; ring
          rwa [he] at hb
        have hTFga : tFwd (a - (B : ZMod P.n)) := ⟨hentry_nbad, hentry_bad1⟩
        have hfwdB : fwd (a - (B : ZMod P.n) + 1) = B := by
          rw [hfwd, Nat.find_eq_iff]
          refine ⟨?_, ?_⟩
          · have he : a - (B : ZMod P.n) + 1 + (B : ZMod P.n) = a + 1 := by ring
            rw [he]; exact hbi1
          · intro s hs hns
            have hb := hbwd_min a (B - 1 - s) (by omega)
            have he : a - ((B - 1 - s : ℕ) : ZMod P.n)
                = a - (B : ZMod P.n) + 1 + (s : ZMod P.n) := by
              rw [Nat.cast_sub (by omega), Nat.cast_sub hB1]; push_cast; ring
            rw [he] at hb; exact hns hb
        rw [hga, hg]; simp only [if_pos hTFga, hfwdB]; ring
      · rw [hg]; simp only [if_neg hTF, if_neg hTB]
  have hgne : ∀ i, i ≠ e → g i ≠ e := by
    intro i hie0
    by_cases hTF : tFwd i
    · have hbi1 : bad (i + 1) := hTF.2
      set F := fwd (i + 1) with hFg
      have hF1 : 1 ≤ F := by
        rw [Nat.one_le_iff_ne_zero]; intro h
        have hs := hfwd_spec (i + 1); rw [← hFg, h] at hs
        simp only [Nat.cast_zero, add_zero] at hs; exact hs hbi1
      have hlast_bad : bad (i + (F : ZMod P.n)) := by
        have hb := hfwd_min (i + 1) (F - 1) (by omega)
        have he : (i + 1) + (((F - 1 : ℕ)) : ZMod P.n) = i + (F : ZMod P.n) := by
          rw [Nat.cast_sub hF1]; push_cast; ring
        rwa [he] at hb
      have hgi : g i = i + (F : ZMod P.n) := by rw [hg]; simp only [if_pos hTF, ← hFg]
      rw [hgi]; intro h; exact hnbe (h ▸ hlast_bad)
    · by_cases hTB : tBwd i
      · have hbi : bad i := hTB.1
        set B := bwd i with hBg
        have hB1 : 1 ≤ B := by
          rw [Nat.one_le_iff_ne_zero]; intro h
          have hs := hbwd_spec i; rw [← hBg, h] at hs
          simp only [Nat.cast_zero, sub_zero] at hs; exact hs hbi
        have hentry_bad1 : bad (i - (B : ZMod P.n) + 1) := by
          have hb := hbwd_min i (B - 1) (by omega)
          have he : i - ((B - 1 : ℕ) : ZMod P.n) = i - (B : ZMod P.n) + 1 := by
            rw [Nat.cast_sub hB1]; push_cast; ring
          rwa [he] at hb
        have hgi : g i = i - (B : ZMod P.n) := by rw [hg]; simp only [if_neg hTF, if_pos hTB, ← hBg]
        rw [hgi]; intro h
        apply hnbe1; rw [← h]; exact hentry_bad1
      · rw [hg]; simp only [if_neg hTF, if_neg hTB]; exact hie0
  filter_upwards [hpair] with q hq
  have hsum : (∑ i ∈ Finset.univ.erase e, (f i q - f i q₀)) = 0 := by
    refine Finset.sum_involution (fun i _ => g i)
      (fun i hi => ?_) (fun i hi hne => ?_)
      (fun i hi => Finset.mem_erase.mpr ⟨hgne i (Finset.ne_of_mem_erase hi), Finset.mem_univ _⟩)
      (fun i _ => hinv i)
    · have := hq i hi; linarith [this]
    · intro hgi
      have := hq i hi
      rw [hgi] at this; apply hne; linarith [this]
  have hwd : (∑ i, (f i q - f i q₀))
      = (∑ i ∈ Finset.univ.erase e, (f i q - f i q₀)) + (f e q - f e q₀) :=
    (Finset.sum_erase_add Finset.univ (fun i => f i q - f i q₀) (Finset.mem_univ e)).symm
  have hwind : P.winding q - P.winding q₀ = ∑ i, (f i q - f i q₀) := by
    unfold LatticePolygon.winding; rw [← Finset.sum_sub_distrib]
  have hkey : P.winding q - P.winding q₀ = f e q - f e q₀ := by
    rw [hwind, hwd, hsum, zero_add]
  show P.winding q - f e q = P.winding q₀ - f e q₀
  linarith [hkey]

/-- **Task 1 core — `winding − edgeWind_e` is locally constant on a ball around the foot.**
For a non-horizontal edge `e` of a simple polygon and an interior foot parameter
`s ∈ (0,1)`, there is a radius `ρ > 0` on which `winding − edgeWind_e` equals its value
at the foot.  Packaged from `winding_sub_edge_eventually_eq_full` at `q₀ = foot e s`:
the foot is off every other edge (`foot_notMem_edgeSeg`), and `e` non-horizontal with
`s ∈ (0,1)` puts the foot's height strictly between the two endpoint heights, so both
`h1e`, `h2e` hold. -/
lemma winding_sub_edge_const_near_foot (hS : P.IsSimple) (e : ZMod P.n)
    (hne : (toReal (P.vert e)).2 ≠ (toReal (P.vert (e + 1))).2)
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    ∃ ρ > 0, ∀ q : ℝ × ℝ, dist q (P.foot e s) < ρ →
      P.winding q - edgeWind (toReal (P.vert e)) (toReal (P.vert (e + 1))) q
        = P.winding (P.foot e s)
          - edgeWind (toReal (P.vert e)) (toReal (P.vert (e + 1))) (P.foot e s) := by
  classical
  set a := toReal (P.vert e) with ha
  set b := toReal (P.vert (e + 1)) with hb
  have hf2 : (P.foot e s).2 = (1 - s) * a.2 + s * b.2 := by
    rw [LatticePolygon.foot, ← ha, ← hb]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have h1e : a.2 ≠ (P.foot e s).2 := by
    rw [hf2]; intro h
    have hz : s * (b.2 - a.2) = 0 := by linarith
    rcases mul_eq_zero.1 hz with h0 | h0
    · exact (ne_of_gt hs.1) h0
    · exact hne (by linarith)
  have h2e : b.2 ≠ (P.foot e s).2 := by
    rw [hf2]; intro h
    have hz : (1 - s) * (b.2 - a.2) = 0 := by linarith
    rcases mul_eq_zero.1 hz with h0 | h0
    · exact absurd h0 (ne_of_gt (by linarith [hs.2] : (0:ℝ) < 1 - s))
    · exact hne (by linarith)
  have hev := winding_sub_edge_eventually_eq_full P (P.foot e s) e
    (fun j hj => foot_notMem_edgeSeg P hS e j hj hs) h1e h2e
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hball⟩ := hev
  exact ⟨ρ, hρ, fun q hq => hball hq⟩

/-- **Task 2 core — the `edgeWind` jump across a straddled non-horizontal edge is `1`.**
For `a.2 ≠ b.2`, a left point `pL` (`cross > 0`) and a right point `pR` (`cross < 0`),
both at heights strictly between `a.2` and `b.2`, the directed-edge winding contribution
jumps by exactly `1` from right to left.  Pure case analysis on the edge direction. -/
lemma edgeWind_jump_one (a b pL pR : ℝ × ℝ) (hne : a.2 ≠ b.2)
    (hLlo : min a.2 b.2 < pL.2) (hLhi : pL.2 < max a.2 b.2)
    (hRlo : min a.2 b.2 < pR.2) (hRhi : pR.2 < max a.2 b.2)
    (hLcross : 0 < cross (b - a) (pL - a)) (hRcross : cross (b - a) (pR - a) < 0) :
    edgeWind a b pL - edgeWind a b pR = 1 := by
  rcases lt_or_gt_of_ne hne with hab | hab
  · rw [min_eq_left hab.le] at hLlo hRlo
    rw [max_eq_right hab.le] at hLhi hRhi
    have hL : edgeWind a b pL = 1 := by
      unfold edgeWind; rw [if_pos ⟨hLlo.le, hLhi, hLcross⟩]
    have hR : edgeWind a b pR = 0 := by
      unfold edgeWind
      rw [if_neg (fun h => absurd h.2.2 (by linarith)),
          if_neg (fun h => absurd h.1 (by linarith))]
    rw [hL, hR]; ring
  · rw [min_eq_right hab.le] at hLlo hRlo
    rw [max_eq_left hab.le] at hLhi hRhi
    have hL : edgeWind a b pL = 0 := by
      unfold edgeWind
      rw [if_neg (fun h => absurd h.1 (by linarith)),
          if_neg (fun h => absurd h.2.2 (by linarith))]
    have hR : edgeWind a b pR = -1 := by
      unfold edgeWind
      rw [if_neg (fun h => absurd h.2.2 (by linarith)),
          if_pos ⟨hRlo.le, hRhi, hRcross⟩]
    rw [hL, hR]; ring

/-- **Tasks 2–3 packaged — a foot-matched left/right pair pins the windings.** For a
simple positively-oriented polygon `P`, a non-horizontal edge `e`, an interior foot
parameter `s ∈ (0,1)`, and `ε > 0`, there is a left-region point `pL` and a right-region
point `pR`, both built over the same foot, with `P.winding pL = 1` and `P.winding pR = 0`.
The jump of `1` comes from `edgeWind_jump_one` (the two points straddle `e` at heights
between the endpoints) carried across by `winding_sub_edge_const_near_foot`; the absolute
value `1` is `leftRegion_winding_one`. -/
lemma exists_foot_pair_windings (hS : P.IsSimple) (hO : P.PositivelyOriented) (e : ZMod P.n)
    (hne : (toReal (P.vert e)).2 ≠ (toReal (P.vert (e + 1))).2)
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ pL ∈ P.leftRegion e ε, ∃ pR ∈ P.rightRegion e ε,
      P.winding pL = 1 ∧ P.winding pR = 0 := by
  classical
  set a := toReal (P.vert e) with ha
  set b := toReal (P.vert (e + 1)) with hb
  -- the foot and its height (strictly between the endpoint heights)
  have hf2 : (P.foot e s).2 = (1 - s) * a.2 + s * b.2 := by
    rw [LatticePolygon.foot, ← ha, ← hb]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  set m := min a.2 b.2 with hm
  set M := max a.2 b.2 with hM
  have hmM : m < (P.foot e s).2 ∧ (P.foot e s).2 < M := by
    rw [hf2, hm, hM]
    rcases lt_or_gt_of_ne hne with hab | hab
    · rw [min_eq_left hab.le, max_eq_right hab.le]
      constructor <;> nlinarith [hs.1, hs.2]
    · rw [min_eq_right hab.le, max_eq_left hab.le]
      constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨hmlt, hMlt⟩ := hmM
  -- the constancy radius near the foot
  obtain ⟨ρ, hρ, hball⟩ := winding_sub_edge_const_near_foot P hS e hne hs
  set η := min ρ (min ((P.foot e s).2 - m) (M - (P.foot e s).2)) with hη
  have hηpos : 0 < η := lt_min hρ (lt_min (by linarith) (by linarith))
  have hηρ : η ≤ ρ := min_le_left _ _
  have hηm : η ≤ (P.foot e s).2 - m := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηM : η ≤ M - (P.foot e s).2 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the offset `t`, small under both the cap and `η`
  set cap := P.capHeight e ε s with hcap
  have hcappos : 0 < cap := capHeight_pos P hS e hε hs
  set t := min (cap / 2) (η / 2) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have htcap : t < cap := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htη : t < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set pL := P.rectMap e (P.leftNormal e) (s, t) with hpLdef
  set pR := P.rectMap e (P.rightNormal e) (s, t) with hpRdef
  have hpLmem : pL ∈ P.leftRegion e ε := ⟨(s, t), ⟨hs, htpos, htcap⟩, rfl⟩
  have hpRmem : pR ∈ P.rightRegion e ε := ⟨(s, t), ⟨hs, htpos, htcap⟩, rfl⟩
  -- distances to the foot equal `t`
  have hdL : dist pL (P.foot e s) = t := by
    rw [hpLdef, dist_rectMap_foot, leftNormal_unit P hS, mul_one, abs_of_pos htpos]
  have hdR : dist pR (P.foot e s) = t := by
    rw [hpRdef, dist_rectMap_foot, rightNormal_unit P hS, mul_one, abs_of_pos htpos]
  -- height control: the second coordinates land strictly between the endpoints
  have habs : ∀ p : ℝ × ℝ, |p.2 - (P.foot e s).2| ≤ dist p (P.foot e s) := by
    intro p
    rw [show |p.2 - (P.foot e s).2| = dist p.2 (P.foot e s).2 from (Real.dist_eq _ _).symm,
      Prod.dist_eq]
    exact le_max_right _ _
  have hheight : ∀ p : ℝ × ℝ, dist p (P.foot e s) = t → m < p.2 ∧ p.2 < M := by
    intro p hp
    have h1 : |p.2 - (P.foot e s).2| < (P.foot e s).2 - m := by
      have := habs p; rw [hp] at this; linarith
    have h2 : |p.2 - (P.foot e s).2| < M - (P.foot e s).2 := by
      have := habs p; rw [hp] at this; linarith
    exact ⟨by linarith [(abs_lt.1 h1).1], by linarith [(abs_lt.1 h2).2]⟩
  obtain ⟨hpL2lo, hpL2hi⟩ := hheight pL hdL
  obtain ⟨hpR2lo, hpR2hi⟩ := hheight pR hdR
  -- cross signs from region membership
  have hed : P.edgeDir e = b - a := by rw [LatticePolygon.edgeDir, ← ha, ← hb]
  have hcrossL : 0 < cross (b - a) (pL - a) := by
    have := rectMap_left_cross_pos P hS e (s := s) (t := t) htpos
    rwa [hed, ← ha, ← hpLdef] at this
  have hcrossR : cross (b - a) (pR - a) < 0 := by
    have := rectMap_right_cross_neg P hS e (s := s) (t := t) htpos
    rwa [hed, ← ha, ← hpRdef] at this
  -- the edge-wind jump is exactly `1`
  have hjump : edgeWind a b pL - edgeWind a b pR = 1 :=
    edgeWind_jump_one a b pL pR hne hpL2lo hpL2hi hpR2lo hpR2hi hcrossL hcrossR
  -- carry the windings across with the constancy radius
  have hbL := hball pL (by rw [hdL]; linarith)
  have hbR := hball pR (by rw [hdR]; linarith)
  rw [← ha, ← hb] at hbL hbR
  have hwL : P.winding pL = 1 := leftRegion_winding_one P hS hO hε e hpLmem
  have hwR : P.winding pR = 0 := by
    have : P.winding pL - P.winding pR = edgeWind a b pL - edgeWind a b pR := by linarith
    rw [hjump] at this; rw [hwL] at this; linarith
  exact ⟨pL, hpLmem, pR, hpRmem, hwL, hwR⟩

/-- **Off-boundary wedge ball at a vertex.** A point `q` strictly to the left of both edges
incident to `vᵢ` (`edge i-1 = [vᵢ₋₁, vᵢ]` and `edge i = [vᵢ, vᵢ₊₁]`) and within `featureSize`
of `vᵢ` is off the boundary: the two strict half-plane signs rule out the two incident edges
(`cross = 0` on the edge line), and feature-size distance rules out every non-incident edge. -/
lemma wedge_ball_off_boundary (P : LatticePolygon) (_ : P.IsSimple) (i : ZMod P.n)
    {q : ℝ × ℝ}
    (h1 : 0 < cross (toReal (P.vert i) - toReal (P.vert (i - 1))) (q - toReal (P.vert i)))
    (h2 : 0 < cross (toReal (P.vert (i + 1)) - toReal (P.vert i)) (q - toReal (P.vert i)))
    (hb : dist q (toReal (P.vert i)) < P.featureSize) :
    q ∉ P.boundary := by
  classical
  intro hqb
  rw [LatticePolygon.boundary, Set.mem_iUnion] at hqb
  obtain ⟨k, hk⟩ := hqb
  by_cases hki1 : k = i - 1
  · rw [hki1, LatticePolygon.edgeSeg, show (i - 1) + 1 = i by ring] at hk
    have hz : cross (toReal (P.vert i) - toReal (P.vert (i - 1)))
        (q - toReal (P.vert (i - 1))) = 0 := cross_seg_zero _ _ q hk
    have hz' : cross (toReal (P.vert i) - toReal (P.vert (i - 1))) (q - toReal (P.vert i)) = 0 := by
      have e : q - toReal (P.vert i)
          = (q - toReal (P.vert (i - 1))) - (toReal (P.vert i) - toReal (P.vert (i - 1))) := by
        abel
      rw [e]
      simp only [cross, Prod.fst_sub, Prod.snd_sub] at hz ⊢
      linear_combination hz
    rw [hz'] at h1; exact lt_irrefl _ h1
  by_cases hki : k = i
  · rw [hki, LatticePolygon.edgeSeg] at hk
    have hz : cross (toReal (P.vert (i + 1)) - toReal (P.vert i)) (q - toReal (P.vert i)) = 0 :=
      cross_seg_zero _ _ q hk
    rw [hz] at h2; exact lt_irrefl _ h2
  · have hle : P.featureSize ≤ Metric.infDist (toReal (P.vert i)) (P.edgeSeg k) :=
      featureSize_le P i k hki hki1
    have hinf : Metric.infDist (toReal (P.vert i)) (P.edgeSeg k) ≤ dist (toReal (P.vert i)) q :=
      Metric.infDist_le_dist_of_mem hk
    rw [dist_comm] at hinf
    linarith

/-- **Task 4 — the open diagonal has winding `1`.** For a simple positively-oriented polygon,
a diagonal `(i, j)` whose far endpoint `vⱼ` lies in the convex corner triangle at `i`
(`0 < cornerCross P i`, `inTriangle`), every point of the open diagonal `openSegment(vᵢ, vⱼ)`
has `P.winding = 1`. The open diagonal is preconnected and off-boundary, so winding is constant
there; a point `p₀` just along the diagonal from `vᵢ` lies in the open interior wedge at the
convex vertex, connected within that wedge (off-boundary, `wedge_ball_off_boundary`) to a
`leftRegion` point of edge `i` (winding `1` by `leftRegion_winding_one`). -/
lemma diag_interior_winding_one (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (i j : ZMod P.n) (hdiag : IsDiagonal P i j) (hconv : 0 < cornerCross P i)
    (hwT : inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
            (toReal (P.vert j)))
    (p : ℝ × ℝ) (hp : p ∈ openSegment ℝ (toReal (P.vert i)) (toReal (P.vert j))) :
    P.winding p = 1 := by
  classical
  set a := toReal (P.vert (i - 1)) with ha
  set b := toReal (P.vert i) with hb
  set c := toReal (P.vert (i + 1)) with hc
  set vj := toReal (P.vert j) with hvj
  obtain ⟨hij, hij1, hji1, hdisj⟩ := hdiag
  have hw2 : j ≠ i := fun h => hij h.symm
  have hw3 : j ≠ i + 1 := fun h => hij1 h.symm
  have hw1 : j ≠ i - 1 := fun h => hji1 (by rw [h]; ring)
  -- corner cross identities
  have hcc : 0 < cross (b - a) (c - b) := by
    have h := hconv; unfold cornerCross at h; rw [← ha, ← hb, ← hc] at h; exact h
  have hbase : 0 < cross (b - a) (c - a) := by
    have e : cross (b - a) (c - a) = cross (b - a) (c - b) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; exact hcc
  -- strict wedge functionals at vⱼ
  have hf1 : 0 < cross (b - a) (vj - b) := by
    have e : cross (b - a) (vj - b) = cross (b - a) (vj - a) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]
    rcases lt_or_eq_of_le hwT.1 with h | h
    · exact h
    · exfalso
      have hmem : vj ∈ segment ℝ a b :=
        mem_segment_ab_of_inTriangle_f1_zero a b c vj hbase hwT h.symm
      have hedge : P.edgeSeg (i - 1) = segment ℝ a b := by
        rw [LatticePolygon.edgeSeg, show (i - 1) + 1 = i by ring, ← ha, ← hb]
      exact vert_notMem_edgeSeg P hS j (i - 1) (Ne.symm hw1)
        (fun he => hw2 (by linear_combination -he)) (hedge ▸ hmem)
  have hf2 : 0 < cross (c - b) (vj - b) := by
    rcases lt_or_eq_of_le hwT.2.1 with h | h
    · exact h
    · exfalso
      have hmem : vj ∈ segment ℝ b c :=
        mem_segment_bc_of_inTriangle_f2_zero a b c vj hbase hwT h.symm
      have hedge : P.edgeSeg i = segment ℝ b c := by
        rw [LatticePolygon.edgeSeg, ← hb, ← hc]
      exact vert_notMem_edgeSeg P hS j i (Ne.symm hw2)
        (fun he => hw3 (by linear_combination -he)) (hedge ▸ hmem)
  -- open diagonal is preconnected and off-boundary
  have hDsub : openSegment ℝ b vj ⊆ P.boundaryᶜ := by
    intro x hx
    rw [Set.mem_compl_iff, LatticePolygon.boundary, Set.mem_iUnion]
    rintro ⟨k, hk⟩
    exact Set.disjoint_left.mp (hdisj k) hx hk
  have hDpre : IsPreconnected (openSegment ℝ b vj) := (convex_openSegment b vj).isPreconnected
  -- generic bilinear-combo facts
  have crosscombo : ∀ (dir base p1 p2 : ℝ × ℝ) (α β : ℝ), α + β = 1 →
      cross dir ((α • p1 + β • p2) - base)
        = α * cross dir (p1 - base) + β * cross dir (p2 - base) := by
    intro dir base p1 p2 α β hαβ
    have hβ : β = 1 - α := by linarith
    subst hβ
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have combo_pos : ∀ (u v A B : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 → 0 < A → 0 < B →
      0 < u * A + v * B := by
    intro u v A B hu hv huv hA hB
    rcases eq_or_lt_of_le hu with h | h
    · simp only [← h, zero_mul, zero_add]
      have hv1 : v = 1 := by linarith
      rw [hv1, one_mul]; exact hB
    · have h1 : 0 < u * A := mul_pos h hA
      have h2 : 0 ≤ v * B := mul_nonneg hv hB.le
      linarith
  have habs_cross : ∀ u w : ℝ × ℝ, |cross u w| ≤ (|u.1| + |u.2|) * ‖w‖ := by
    intro u w
    rw [cross, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |w.1| ≤ max |w.1| |w.2| := le_max_left _ _
    have h2 : |w.2| ≤ max |w.1| |w.2| := le_max_right _ _
    calc |u.1 * w.2 - u.2 * w.1|
          ≤ |u.1 * w.2| + |u.2 * w.1| := abs_sub _ _
      _ = |u.1| * |w.2| + |u.2| * |w.1| := by rw [abs_mul, abs_mul]
      _ ≤ (|u.1| + |u.2|) * max |w.1| |w.2| := by
          nlinarith [abs_nonneg u.1, abs_nonneg u.2, h1, h2]
  have hfs : 0 < P.featureSize := featureSize_pos P hS
  -- the diagonal witness p₀ near vᵢ
  set σ := min (1 / 2 : ℝ) (P.featureSize / (2 * (‖vj - b‖ + 1))) with hσdef
  have hσpos : 0 < σ := lt_min (by norm_num) (by positivity)
  have hσlt1 : σ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hσfs : σ * ‖vj - b‖ < P.featureSize := by
    have h1 : σ ≤ P.featureSize / (2 * (‖vj - b‖ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [h1, hσpos, norm_nonneg (vj - b), hfs]
  set p₀ := (1 - σ) • b + σ • vj with hp₀def
  have hp₀mem : p₀ ∈ openSegment ℝ b vj :=
    ⟨1 - σ, σ, by linarith, hσpos, by ring, rfl⟩
  have hp0sub : p₀ - b = σ • (vj - b) := by rw [hp₀def]; module
  have hp0b : dist p₀ b < P.featureSize := by
    rw [dist_eq_norm, hp0sub, norm_smul, Real.norm_eq_abs, abs_of_pos hσpos]; exact hσfs
  have hw1p0 : 0 < cross (b - a) (p₀ - b) := by
    rw [hp0sub]
    have e : cross (b - a) (σ • (vj - b)) = σ * cross (b - a) (vj - b) := by
      simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hσpos hf1
  have hw2p0 : 0 < cross (c - b) (p₀ - b) := by
    rw [hp0sub]
    have e : cross (c - b) (σ • (vj - b)) = σ * cross (c - b) (vj - b) := by
      simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hσpos hf2
  -- the interior leftRegion witness pL near vᵢ
  set nL := P.leftNormal i with hnL
  have hnLunit : ‖nL‖ = 1 := leftNormal_unit P hS i
  set M := |(b - a).1| + |(b - a).2| with hMdef
  have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  set s' := min (1 / 2 : ℝ) (P.featureSize / (2 * (‖c - b‖ + 1))) with hs'def
  have hs'pos : 0 < s' := lt_min (by norm_num) (by positivity)
  have hs'lt1 : s' < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hs'mem : s' ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs'pos, hs'lt1⟩
  have hs'cb : s' * (‖c - b‖ + 1) ≤ P.featureSize / 2 := by
    have h1 : s' ≤ P.featureSize / (2 * (‖c - b‖ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1; nlinarith [h1]
  set cap := P.capHeight i P.featureSize s' with hcapdef
  have hcappos : 0 < cap := capHeight_pos P hS i hfs hs'mem
  have hnum : 0 < s' * cross (b - a) (c - b) / (2 * (M + 1)) :=
    div_pos (mul_pos hs'pos hcc) (by positivity)
  set t' := min (s' * cross (b - a) (c - b) / (2 * (M + 1))) (min (cap / 2) (P.featureSize / 4))
    with ht'def
  have ht'pos : 0 < t' := lt_min hnum (lt_min (by positivity) (by positivity))
  have ht'A : t' ≤ s' * cross (b - a) (c - b) / (2 * (M + 1)) := min_le_left _ _
  have ht'cap : t' < cap :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have ht'fs4 : t' ≤ P.featureSize / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  set pL := P.rectMap i nL (s', t') with hpLdef
  have hpLmem : pL ∈ P.leftRegion i P.featureSize :=
    ⟨(s', t'), ⟨hs'mem, ht'pos, ht'cap⟩, rfl⟩
  have hwL : P.winding pL = 1 := leftRegion_winding_one P hS hO hfs i hpLmem
  have hpLeq : pL = (1 - s') • b + s' • c + t' • nL := by
    rw [hpLdef, LatticePolygon.rectMap, ← hb, ← hc]
  have hpLsub : pL - b = s' • (c - b) + t' • nL := by rw [hpLeq]; module
  have hedgeDir : P.edgeDir i = c - b := by rw [LatticePolygon.edgeDir, ← hb, ← hc]
  have hw2pL : 0 < cross (c - b) (pL - b) := by
    have h := rectMap_left_cross_pos P hS i (s := s') (t := t') ht'pos
    rw [hedgeDir, ← hb] at h
    exact h
  have hKbd : |cross (b - a) nL| ≤ M := by
    have := habs_cross (b - a) nL
    rw [hnLunit, mul_one] at this
    rw [hMdef]; exact this
  have hw1pL : 0 < cross (b - a) (pL - b) := by
    rw [hpLsub]
    have hexp : cross (b - a) (s' • (c - b) + t' • nL)
        = s' * cross (b - a) (c - b) + t' * cross (b - a) nL := by
      simp only [cross, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      ring
    rw [hexp]
    have hK : -M ≤ cross (b - a) nL := neg_le_of_abs_le hKbd
    have ht'mul : t' * (2 * (M + 1)) ≤ s' * cross (b - a) (c - b) := by
      have h := ht'A; rwa [le_div_iff₀ (by positivity)] at h
    nlinarith [hK, ht'mul, ht'pos, hMnn, hs'pos, hcc,
      mul_le_mul_of_nonneg_left hK ht'pos.le]
  have hpLb : dist pL b < P.featureSize := by
    rw [dist_eq_norm, hpLsub]
    calc ‖s' • (c - b) + t' • nL‖ ≤ ‖s' • (c - b)‖ + ‖t' • nL‖ := norm_add_le _ _
      _ = s' * ‖c - b‖ + t' * 1 := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hs'pos, abs_of_pos ht'pos, hnLunit]
      _ < P.featureSize := by nlinarith [hs'cb, ht'fs4, hfs, hs'pos, norm_nonneg (c - b)]
  -- connect pL to p₀ inside the off-boundary wedge ball
  have hseg : ∀ z ∈ segment ℝ pL p₀, z ∉ P.boundary := by
    intro z hzmem
    obtain ⟨u, v, hu, hv, huv, hzeq⟩ := hzmem
    apply wedge_ball_off_boundary P hS i
    · have hcz : cross (b - a) (z - b)
          = u * cross (b - a) (pL - b) + v * cross (b - a) (p₀ - b) := by
        rw [← hzeq]; exact crosscombo (b - a) b pL p₀ u v huv
      rw [hcz]; exact combo_pos u v _ _ hu hv huv hw1pL hw1p0
    · have hcz : cross (c - b) (z - b)
          = u * cross (c - b) (pL - b) + v * cross (c - b) (p₀ - b) := by
        rw [← hzeq]; exact crosscombo (c - b) b pL p₀ u v huv
      rw [hcz]; exact combo_pos u v _ _ hu hv huv hw2pL hw2p0
    · have hzball := (convex_ball b P.featureSize).segment_subset
        (Metric.mem_ball.mpr hpLb) (Metric.mem_ball.mpr hp0b) ⟨u, v, hu, hv, huv, hzeq⟩
      exact Metric.mem_ball.mp hzball
  have hwp0 : P.winding p₀ = 1 := by
    rw [winding_const_of_isPreconnected P (fun z hz => hseg z hz)
      (convex_segment pL p₀).isPreconnected (right_mem_segment ℝ pL p₀)
      (left_mem_segment ℝ pL p₀)]
    exact hwL
  rw [winding_const_of_isPreconnected P hDsub hDpre hp hp₀mem]
  exact hwp0

/-- Every vertex lies on the boundary (left endpoint of its edge). -/
lemma vert_mem_boundary (P : LatticePolygon) (k : ZMod P.n) :
    toReal (P.vert k) ∈ P.boundary :=
  Set.mem_iUnion.mpr ⟨k, by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩

/-- **A simple polygon has a non-horizontal edge.** If every edge were horizontal, all
vertex heights would be equal and the shoelace would vanish, contradicting
`shoelace_ne_zero_of_isSimple`. -/
lemma exists_nonhoriz_edge (Q : LatticePolygon) (hSQ : Q.IsSimple) :
    ∃ k : ZMod Q.n, (toReal (Q.vert k)).2 ≠ (toReal (Q.vert (k + 1))).2 := by
  classical
  by_contra hcon
  push Not at hcon
  apply shoelace_ne_zero_of_isSimple Q hSQ
  rw [LatticePolygon.shoelace]
  have hsum : ∑ k : ZMod Q.n, cross (toReal (Q.vert k)) (toReal (Q.vert (k + 1))) = 0 := by
    have e1 : ∀ k : ZMod Q.n, cross (toReal (Q.vert k)) (toReal (Q.vert (k + 1)))
        = (toReal (Q.vert k)).2 * (toReal (Q.vert k)).1
          - (toReal (Q.vert k)).2 * (toReal (Q.vert (k + 1))).1 := by
      intro k
      rw [cross, ← hcon k]; ring
    rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_sub_distrib]
    have e2 : ∑ k : ZMod Q.n, (toReal (Q.vert k)).2 * (toReal (Q.vert (k + 1))).1
        = ∑ k : ZMod Q.n, (toReal (Q.vert k)).2 * (toReal (Q.vert k)).1 := by
      rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod Q.n))
        (fun m => (toReal (Q.vert m)).2 * (toReal (Q.vert m)).1)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Equiv.coe_addRight]
      rw [hcon k]
    rw [e2]; ring
  rw [hsum]; norm_num

/-- **Telescoping height argument.** If `vert 0` and `vert m` differ in height, some
consecutive arc pair `p, p+1` (`p < m`) does too. -/
lemma exists_consec_ne (Q : LatticePolygon) (m : ℕ) (_ : m < Q.n)
    (hne : (toReal (Q.vert ((m : ℕ) : ZMod Q.n))).2 ≠ (toReal (Q.vert 0)).2) :
    ∃ p : ℕ, p < m ∧
      (toReal (Q.vert ((p : ℕ) : ZMod Q.n))).2
        ≠ (toReal (Q.vert (((p + 1 : ℕ) : ZMod Q.n)))).2 := by
  by_contra hcon
  push Not at hcon
  apply hne
  have key : ∀ p : ℕ, p ≤ m → (toReal (Q.vert ((p : ℕ) : ZMod Q.n))).2
      = (toReal (Q.vert 0)).2 := by
    intro p
    induction p with
    | zero => intro _; simp
    | succ q ih =>
      intro hp
      have hqm : q < m := by omega
      rw [← ih (by omega)]
      exact (hcon q hqm).symm
  exact key m (le_refl m)

/-- **A non-horizontal kept (arc) edge of `splitPoly P i j` exists.** From
`exists_nonhoriz_edge` on the (simple) arc polygon; if the witnessed non-horizontal edge is
the diagonal then `vᵢ.2 ≠ vⱼ.2`, and `exists_consec_ne` produces a non-horizontal arc edge. -/
lemma exists_nonhoriz_arc_edge (P : LatticePolygon) (hS : P.IsSimple) (h2 : 2 ≤ P.n)
    (i j : ZMod P.n) (hdiag : IsDiagonal P i j) :
    ∃ k : ZMod (splitPoly P i j).n, k.val < (j - i).val ∧
      (toReal ((splitPoly P i j).vert k)).2 ≠ (toReal ((splitPoly P i j).vert (k + 1))).2 := by
  classical
  obtain ⟨hij, hij1, hji1, hdisj⟩ := hdiag
  have hSL : (splitPoly P i j).IsSimple :=
    splitPoly_isSimple_of_diagonal P hS h2 i j ⟨hij, hij1, hji1, hdisj⟩
  set L := splitPoly P i j with hLdef
  have hN : L.n = (j - i).val + 1 := rfl
  obtain ⟨k0, hk0⟩ := exists_nonhoriz_edge L hSL
  rcases splitPoly_idx_dichotomy P i j k0 with hlt | heq
  · exact ⟨k0, hlt, hk0⟩
  · -- diagonal case: derive vⱼ.2 ≠ vᵢ.2, then telescope
    have hvk0 : L.vert k0 = P.vert j := by
      rw [splitPoly_vert, heq, ZMod.natCast_zmod_val]
      congr 1; ring
    have hk01 : k0 + 1 = 0 := by
      have hcast : (k0 + 1) = ((k0.val + 1 : ℕ) : ZMod L.n) := by
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [hcast, heq, show ((j - i).val + 1 : ℕ) = L.n from hN.symm]
      exact_mod_cast ZMod.natCast_self _
    have hvk01 : L.vert (k0 + 1) = P.vert i := by
      rw [hk01, splitPoly_vert, ZMod.val_zero, Nat.cast_zero, add_zero]
    rw [hvk0, hvk01] at hk0
    -- hk0 : (P.vert j).2 ≠ (P.vert i).2
    have hk0i : ((j - i).val : ZMod L.n) = k0 := by
      rw [← heq, ZMod.natCast_zmod_val]
    have hmlt : (j - i).val < L.n := by rw [hN]; omega
    obtain ⟨p, hpm, hpne⟩ := exists_consec_ne L (j - i).val hmlt
      (by
        have h0 : L.vert 0 = P.vert i := by rw [splitPoly_vert, ZMod.val_zero, Nat.cast_zero, add_zero]
        rw [hk0i, hvk0, h0]; exact hk0)
    refine ⟨(p : ZMod L.n), ?_, ?_⟩
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; exact hpm
    · have hcast : ((p : ZMod L.n) + 1) = ((p + 1 : ℕ) : ZMod L.n) := by push_cast; ring
      rw [hcast]; exact hpne

/-- **A far winding-`0` exterior witness beyond any radius `R₀`.** Variant of
`exterior_reaches_far` whose far point can be required arbitrarily far out (needed to match a
*second* polygon's cobounded radius). -/
lemma exterior_reaches_far_beyond (P : LatticePolygon) (hS : P.IsSimple) {q : ℝ × ℝ}
    (hqb : q ∉ P.boundary) (hqw : P.winding q = 0) (R₀ : ℝ) :
    ∃ S : Set (ℝ × ℝ), S ⊆ P.boundaryᶜ ∧ IsPreconnected S ∧ q ∈ S ∧
      ∃ q₀ ∈ S, R₀ < ‖q₀‖ := by
  classical
  obtain ⟨A, B, hAB, hApc, hBpc⟩ := compl_boundary_atMost_two P hS
  have hAsub : A ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_left
  have hBsub : B ⊆ P.boundaryᶜ := by rw [← hAB]; exact Set.subset_union_right
  obtain ⟨Rw, hRw⟩ := winding_zero_on_cobounded P
  have hbd : Bornology.IsBounded P.boundary := by
    unfold LatticePolygon.boundary
    rw [Bornology.isBounded_iUnion]
    intro i
    unfold LatticePolygon.edgeSeg
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isBounded
  obtain ⟨Rb, hRb⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hbd
  set c : ℝ := |Rw| + |Rb| + |R₀| + 1 with hc
  have hcnn : (0 : ℝ) ≤ c := by positivity
  have hcnorm : ‖((c : ℝ), (0 : ℝ))‖ = c := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_zero,
      max_eq_left (abs_nonneg _), abs_of_nonneg hcnn]
  have hcR : Rw < c := by
    rw [hc]; have := le_abs_self Rw; have := abs_nonneg Rb; have := abs_nonneg R₀; linarith
  have hcRb : Rb < c := by
    rw [hc]; have := le_abs_self Rb; have := abs_nonneg Rw; have := abs_nonneg R₀; linarith
  have hcR0 : R₀ < c := by
    rw [hc]; have := le_abs_self R₀; have := abs_nonneg Rw; have := abs_nonneg Rb; linarith
  set qf : ℝ × ℝ := (c, 0) with hqf
  have hqfb : qf ∉ P.boundary := by
    intro hmem
    have hmem2 := hRb hmem
    rw [Metric.mem_closedBall, dist_zero_right, hqf, hcnorm] at hmem2
    linarith
  have hqfw : P.winding qf = 0 := hRw qf (by rw [hqf, hcnorm]; exact hcR)
  have hqfnorm : R₀ < ‖qf‖ := by rw [hqf, hcnorm]; exact hcR0
  obtain ⟨p1, hp1b, hp1w⟩ := exists_abs_winding_eq_one_of_isSimple P hS
  have hp1ne : P.winding p1 ≠ 0 := by rcases hp1w with h | h <;> rw [h] <;> norm_num
  have hqAB : q ∈ A ∪ B := by rw [hAB]; exact hqb
  have hqfAB : qf ∈ A ∪ B := by rw [hAB]; exact hqfb
  have hp1AB : p1 ∈ A ∪ B := by rw [hAB]; exact hp1b
  rcases hp1AB with hp1A | hp1B
  · refine ⟨B, hBsub, hBpc, ?_, qf, ?_, hqfnorm⟩
    · rcases hqAB with hqA | hqB
      · exact absurd ((winding_const_of_isPreconnected P hAsub hApc hp1A hqA).trans hqw) hp1ne
      · exact hqB
    · rcases hqfAB with hqfA | hqfB
      · exact absurd ((winding_const_of_isPreconnected P hAsub hApc hp1A hqfA).trans hqfw) hp1ne
      · exact hqfB
  · refine ⟨A, hAsub, hApc, ?_, qf, ?_, hqfnorm⟩
    · rcases hqAB with hqA | hqB
      · exact hqA
      · exact absurd ((winding_const_of_isPreconnected P hBsub hBpc hp1B hqB).trans hqw) hp1ne
    · rcases hqfAB with hqfA | hqfB
      · exact hqfA
      · exact absurd ((winding_const_of_isPreconnected P hBsub hBpc hp1B hqfB).trans hqfw) hp1ne

/-- **A `P`-exterior point is `splitPoly`-exterior.** Given Task 4 (`hDwind`: the open
diagonal has winding `1`), any off-boundary `q` with `P.winding q = 0` has
`(splitPoly P i j).winding q = 0`: the `P`-exterior set reaching infinity stays off
`splitPoly`'s boundary (which is `P.boundary ∪` the closed diagonal — and the exterior set,
being winding-`0`, avoids the winding-`1` open diagonal and the two boundary endpoints). -/
lemma split_winding_zero_of_P_exterior (P : LatticePolygon) (hS : P.IsSimple)
    (_ : 2 ≤ P.n) (i j : ZMod P.n)
    (hDwind : ∀ p ∈ openSegment ℝ (toReal (P.vert i)) (toReal (P.vert j)), P.winding p = 1)
    {q : ℝ × ℝ} (hqP : q ∉ P.boundary) (hqw : P.winding q = 0) :
    (splitPoly P i j).winding q = 0 := by
  classical
  set L := splitPoly P i j with hLdef
  obtain ⟨Rc, hRc⟩ := winding_zero_on_cobounded L
  obtain ⟨S, hSsub, hSpre, hqS, q₀, hq₀S, hq₀far⟩ :=
    exterior_reaches_far_beyond P hS hqP hqw Rc
  have hSL : S ⊆ L.boundaryᶜ := by
    intro x hx
    have hxP : x ∉ P.boundary := hSsub hx
    have hxw : P.winding x = 0 := by
      rw [winding_const_of_isPreconnected P hSsub hSpre hx hqS]; exact hqw
    rw [Set.mem_compl_iff]
    intro hxLb
    rcases splitPoly_boundary_subset P i j hxLb with hxPb | hxD
    · exact hxP hxPb
    · -- hxD : x ∈ segment ℝ (toReal (P.vert j)) (toReal (P.vert i))
      by_cases hxj : x = toReal (P.vert j)
      · exact hxP (hxj ▸ vert_mem_boundary P j)
      by_cases hxi : x = toReal (P.vert i)
      · exact hxP (hxi ▸ vert_mem_boundary P i)
      · have hxo : x ∈ openSegment ℝ (toReal (P.vert j)) (toReal (P.vert i)) :=
          mem_openSegment_of_ne_ends hxD hxj hxi
        have hxo' : x ∈ openSegment ℝ (toReal (P.vert i)) (toReal (P.vert j)) := by
          rwa [openSegment_symm] at hxo
        rw [hDwind x hxo'] at hxw; norm_num at hxw
  exact winding_zero_of_joinedIn_far L ⟨S, hSL, hSpre, hqS, hq₀S⟩ ⟨Rc, hRc, hq₀far⟩

/-- **One split-half separation witness.** For a diagonal `(i, j)` with Task 4 (`hDwind`),
there is a point `pL` off both `splitPoly P i j` and `P` boundaries with
`(splitPoly P i j).winding pL ≠ 0` and `(splitPoly P j i).winding pL = 0`. Built over a
non-horizontal *arc* edge (shared between `P` and the arc polygon `L := splitPoly P i j`):
a `leftRegion` point `pL` (interior, `P.winding = 1`) and its mirror `rightRegion` point `pR`
(exterior, `P.winding = 0`). The `L`-winding jump across the shared edge
(`winding_sub_edge_const_near_foot` for `L`, `edgeWind_jump_one`) plus `L.winding pR = 0`
(`pR` is `P`-exterior, `split_winding_zero_of_P_exterior`) give `L.winding pL = 1`; additivity
(`winding_split_add`) gives `(splitPoly P j i).winding pL = 0`. -/
lemma split_half_witness (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (h2 : 2 ≤ P.n) (i j : ZMod P.n) (hdiag : IsDiagonal P i j)
    (hDwind : ∀ p ∈ openSegment ℝ (toReal (P.vert i)) (toReal (P.vert j)), P.winding p = 1) :
    ∃ pL, pL ∉ (splitPoly P i j).boundary ∧ pL ∉ P.boundary ∧
        (splitPoly P i j).winding pL ≠ 0 ∧ (splitPoly P j i).winding pL = 0 := by
  classical
  obtain ⟨kL, hkLlt, hkLne⟩ := exists_nonhoriz_arc_edge P hS h2 i j hdiag
  obtain ⟨hij, hij1, hji1, hdisj⟩ := hdiag
  have hSL : (splitPoly P i j).IsSimple :=
    splitPoly_isSimple_of_diagonal P hS h2 i j ⟨hij, hij1, hji1, hdisj⟩
  set e := i + ((kL.val : ℕ) : ZMod P.n) with hedef
  -- vertex / edge identifications between the shared arc edge and `P` (before `set L`)
  have hvkL : toReal ((splitPoly P i j).vert kL) = toReal (P.vert e) := rfl
  have hidx : i + (((kL + 1).val : ℕ) : ZMod P.n) = e + 1 := by
    rw [splitPoly_idx_succ P i j kL hkLlt, hedef]; ring
  have hvkL1 : toReal ((splitPoly P i j).vert (kL + 1)) = toReal (P.vert (e + 1)) := by
    show toReal (P.vert (i + (((kL + 1).val : ℕ) : ZMod P.n))) = toReal (P.vert (e + 1))
    rw [hidx]
  have hne : (toReal (P.vert e)).2 ≠ (toReal (P.vert (e + 1))).2 := by
    rw [← hvkL, ← hvkL1]; exact hkLne
  have hvkLL : toReal ((splitPoly P i j).vert kL) = toReal (P.vert e) := by
    rw [hedef]; exact congrArg toReal (splitPoly_vert P i j kL)
  have hvkL1L : toReal ((splitPoly P i j).vert (kL + 1)) = toReal (P.vert (e + 1)) := by
    rw [← hidx]; exact congrArg toReal (splitPoly_vert P i j (kL + 1))
  have hneL : (toReal ((splitPoly P i j).vert kL)).2 ≠ (toReal ((splitPoly P i j).vert (kL + 1))).2 := by
    rw [hvkLL, hvkL1L]; exact hne
  set a := toReal (P.vert e) with ha
  set b := toReal (P.vert (e + 1)) with hb
  set s := (1 / 2 : ℝ) with hsdef
  have hs : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hε : (0 : ℝ) < 1 := one_pos
  have hfooteq : (splitPoly P i j).foot kL s = P.foot e s := by
    rw [LatticePolygon.foot, LatticePolygon.foot, hvkLL, hvkL1L]
  have hrectL : ∀ (nrm : ℝ × ℝ) (st : ℝ × ℝ), (splitPoly P i j).rectMap kL nrm st = P.rectMap e nrm st := by
    intro nrm st
    rw [LatticePolygon.rectMap, LatticePolygon.rectMap, hvkLL, hvkL1L]
  have hnLeq : (splitPoly P i j).leftNormal kL = P.leftNormal e := by
    rw [LatticePolygon.leftNormal, LatticePolygon.leftNormal, LatticePolygon.edgeDir,
      LatticePolygon.edgeDir, hvkLL, hvkL1L]
  have hnReq : (splitPoly P i j).rightNormal kL = P.rightNormal e := by
    rw [LatticePolygon.rightNormal, LatticePolygon.rightNormal, LatticePolygon.edgeDir,
      LatticePolygon.edgeDir, hvkLL, hvkL1L]
  -- constancy radii for the two winding jumps
  obtain ⟨ρP, hρP, hballP⟩ := winding_sub_edge_const_near_foot P hS e hne hs
  obtain ⟨ρL, hρL, hballL⟩ := winding_sub_edge_const_near_foot (splitPoly P i j) hSL kL hneL hs
  have hcapPpos : 0 < P.capHeight e 1 s := capHeight_pos P hS e hε hs
  have hcapLpos : 0 < (splitPoly P i j).capHeight kL 1 s := capHeight_pos (splitPoly P i j) hSL kL hε hs
  -- foot height strictly between endpoint heights
  have hf2 : (P.foot e s).2 = (1 - s) * a.2 + s * b.2 := by
    rw [LatticePolygon.foot, ← ha, ← hb]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  set mlo := min a.2 b.2 with hmlo
  set Mhi := max a.2 b.2 with hMhi
  have hmM : mlo < (P.foot e s).2 ∧ (P.foot e s).2 < Mhi := by
    rw [hf2, hmlo, hMhi]
    rcases lt_or_gt_of_ne hne with hab | hab
    · rw [min_eq_left hab.le, max_eq_right hab.le]; constructor <;> nlinarith [hs.1, hs.2]
    · rw [min_eq_right hab.le, max_eq_left hab.le]; constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨hmlt, hMlt⟩ := hmM
  set η := min ((P.foot e s).2 - mlo) (Mhi - (P.foot e s).2) with hη
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  -- the offset, small under all five constraints
  set t := min (min (P.capHeight e 1 s / 2) ((splitPoly P i j).capHeight kL 1 s / 2))
              (min (η / 2) (min (ρP / 2) (ρL / 2))) with htdef
  have htpos : 0 < t :=
    lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have htcapP : t < P.capHeight e 1 s :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have htcapL : t < (splitPoly P i j).capHeight kL 1 s :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have htη : t < η :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have htρP : t < ρP :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      (by linarith)
  have htρL : t < ρL :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      (by linarith)
  have hηm : η ≤ (P.foot e s).2 - mlo := min_le_left _ _
  have hηM : η ≤ Mhi - (P.foot e s).2 := min_le_right _ _
  -- the matched left/right pair over the shared edge
  set pL := P.rectMap e (P.leftNormal e) (s, t) with hpLdef
  set pR := P.rectMap e (P.rightNormal e) (s, t) with hpRdef
  have hpLmemP : pL ∈ P.leftRegion e 1 := ⟨(s, t), ⟨hs, htpos, htcapP⟩, rfl⟩
  have hpRmemP : pR ∈ P.rightRegion e 1 := ⟨(s, t), ⟨hs, htpos, htcapP⟩, rfl⟩
  have hpLmemL : pL ∈ (splitPoly P i j).leftRegion kL 1 := by
    refine ⟨(s, t), ⟨hs, htpos, htcapL⟩, ?_⟩
    rw [hrectL, hnLeq]
  have hpRmemL : pR ∈ (splitPoly P i j).rightRegion kL 1 := by
    refine ⟨(s, t), ⟨hs, htpos, htcapL⟩, ?_⟩
    rw [hrectL, hnReq]
  have hwLwind : P.winding pL = 1 := leftRegion_winding_one P hS hO hε e hpLmemP
  have hpLP : pL ∉ P.boundary := leftRegion_notMem_boundary P hS e hpLmemP
  have hpLL : pL ∉ (splitPoly P i j).boundary :=
    leftRegion_notMem_boundary (splitPoly P i j) hSL kL hpLmemL
  have hpRP : pR ∉ P.boundary := rightRegion_notMem_boundary P hS e hpRmemP
  -- distances to the (common) foot
  have hdL : dist pL (P.foot e s) = t := by
    rw [hpLdef, dist_rectMap_foot, leftNormal_unit P hS, mul_one, abs_of_pos htpos]
  have hdR : dist pR (P.foot e s) = t := by
    rw [hpRdef, dist_rectMap_foot, rightNormal_unit P hS, mul_one, abs_of_pos htpos]
  -- height control
  have habs : ∀ p : ℝ × ℝ, |p.2 - (P.foot e s).2| ≤ dist p (P.foot e s) := by
    intro p
    rw [show |p.2 - (P.foot e s).2| = dist p.2 (P.foot e s).2 from (Real.dist_eq _ _).symm,
      Prod.dist_eq]
    exact le_max_right _ _
  have hheight : ∀ p : ℝ × ℝ, dist p (P.foot e s) = t → mlo < p.2 ∧ p.2 < Mhi := by
    intro p hp
    have h1 : |p.2 - (P.foot e s).2| < (P.foot e s).2 - mlo := by
      have := habs p; rw [hp] at this; linarith
    have h2 : |p.2 - (P.foot e s).2| < Mhi - (P.foot e s).2 := by
      have := habs p; rw [hp] at this; linarith
    exact ⟨by linarith [(abs_lt.1 h1).1], by linarith [(abs_lt.1 h2).2]⟩
  obtain ⟨hpL2lo, hpL2hi⟩ := hheight pL hdL
  obtain ⟨hpR2lo, hpR2hi⟩ := hheight pR hdR
  have hed : P.edgeDir e = b - a := by rw [LatticePolygon.edgeDir, ← ha, ← hb]
  have hcrossL : 0 < cross (b - a) (pL - a) := by
    have := rectMap_left_cross_pos P hS e (s := s) (t := t) htpos
    rwa [hed, ← ha, ← hpLdef] at this
  have hcrossR : cross (b - a) (pR - a) < 0 := by
    have := rectMap_right_cross_neg P hS e (s := s) (t := t) htpos
    rwa [hed, ← ha, ← hpRdef] at this
  have hjump : edgeWind a b pL - edgeWind a b pR = 1 :=
    edgeWind_jump_one a b pL pR hne hpL2lo hpL2hi hpR2lo hpR2hi hcrossL hcrossR
  -- `P`-side: `pR` is `P`-exterior
  have hbLP := hballP pL (by rw [hdL]; linarith)
  have hbRP := hballP pR (by rw [hdR]; linarith)
  rw [← ha, ← hb] at hbLP hbRP
  have hwR0 : P.winding pR = 0 := by
    have h1 : P.winding pL - P.winding pR = edgeWind a b pL - edgeWind a b pR := by
      linarith [hbLP, hbRP]
    rw [hjump, hwLwind] at h1; linarith
  -- `(splitPoly P i j)`-side jump: `(splitPoly P i j).winding pL - (splitPoly P i j).winding pR = 1`
  have hbLL := hballL pL (by rw [hfooteq, hdL]; exact htρL)
  have hbRL := hballL pR (by rw [hfooteq, hdR]; exact htρL)
  rw [hvkLL, hvkL1L] at hbLL hbRL
  have hwLL : (splitPoly P i j).winding pL - (splitPoly P i j).winding pR = edgeWind a b pL - edgeWind a b pR := by
    linarith [hbLL, hbRL]
  rw [hjump] at hwLL
  have hLR0 : (splitPoly P i j).winding pR = 0 :=
    split_winding_zero_of_P_exterior P hS h2 i j hDwind hpRP hwR0
  have hLL1 : (splitPoly P i j).winding pL = 1 := by rw [hLR0] at hwLL; linarith
  have hsplitR : (splitPoly P j i).winding pL = 0 := by
    have hadd : (splitPoly P i j).winding pL + (splitPoly P j i).winding pL = P.winding pL :=
      winding_split_add P i j hij pL
    rw [hLL1, hwLwind] at hadd; linarith
  exact ⟨pL, hpLL, hpLP, by rw [hLL1]; norm_num, hsplitR⟩

/-- **Task 5 — both split-half separation witnesses.** For a diagonal `(i, j)` with the far
endpoint inside the convex corner at `i`, the two arc polygons have the separation witnesses
required by `splitPoly_hdisj_of_witnesses` / `splitPoly_positivelyOriented_of_witnesses`: each
half's filled region has a point outside the other half. Both follow from `split_half_witness`
(applied to `(i,j)` and the reversed diagonal `(j,i)`), pinned to winding `1` on the open
diagonal by Task 4 (`diag_interior_winding_one`). -/
lemma exists_split_separation_witness (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) (h2 : 2 ≤ P.n) (i j : ZMod P.n) (hdiag : IsDiagonal P i j)
    (hconv : 0 < cornerCross P i)
    (hwT : inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
            (toReal (P.vert j))) :
    (∃ pL, pL ∉ (splitPoly P i j).boundary ∧ pL ∉ P.boundary ∧
        (splitPoly P i j).winding pL ≠ 0 ∧ (splitPoly P j i).winding pL = 0) ∧
    (∃ pR, pR ∉ (splitPoly P j i).boundary ∧ pR ∉ P.boundary ∧
        (splitPoly P j i).winding pR ≠ 0 ∧ (splitPoly P i j).winding pR = 0) := by
  obtain ⟨hij, hij1, hji1, hdisj⟩ := hdiag
  have hDwind : ∀ p ∈ openSegment ℝ (toReal (P.vert i)) (toReal (P.vert j)), P.winding p = 1 :=
    fun p hp => diag_interior_winding_one P hS hO i j ⟨hij, hij1, hji1, hdisj⟩ hconv hwT p hp
  have hdiag' : IsDiagonal P j i := by
    refine ⟨fun h => hij h.symm, hji1, hij1, fun k => ?_⟩
    rw [openSegment_symm]; exact hdisj k
  have hDwind' : ∀ p ∈ openSegment ℝ (toReal (P.vert j)) (toReal (P.vert i)), P.winding p = 1 := by
    intro p hp; rw [openSegment_symm] at hp; exact hDwind p hp
  exact ⟨split_half_witness P hS hO h2 i j ⟨hij, hij1, hji1, hdisj⟩ hDwind,
    split_half_witness P hS hO h2 j i hdiag' hDwind'⟩

/-! ### Step A — both split halves are positively oriented

Assembling `splitPoly_positivelyOriented_of_witnesses` (Step's positive-orientation packaging,
given simplicity of both halves and the two separation witnesses) with the simplicity
(`splitPoly_isSimple_of_diagonal`) and the separation witnesses
(`exists_split_separation_witness`). The witness lemma needs the convex apex (`0 < cornerCross`)
and the far endpoint inside the corner triangle (`inTriangle … (vert j)`), both available from
the deepest-contained selection that produced the diagonal. -/
lemma splitPoly_positivelyOriented (P : LatticePolygon) (hS : P.IsSimple)
    (hO : P.PositivelyOriented) (h2 : 2 ≤ P.n) (i j : ZMod P.n)
    (hdiag : IsDiagonal P i j) (hconv : 0 < cornerCross P i)
    (hwT : inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i)) (toReal (P.vert (i + 1)))
            (toReal (P.vert j))) :
    (splitPoly P i j).PositivelyOriented ∧ (splitPoly P j i).PositivelyOriented := by
  obtain ⟨hij, hij1, hji1, hdisj⟩ := hdiag
  have hdiagD : IsDiagonal P i j := ⟨hij, hij1, hji1, hdisj⟩
  have hdiag' : IsDiagonal P j i := by
    refine ⟨fun h => hij h.symm, hji1, hij1, fun k => ?_⟩
    rw [openSegment_symm]; exact hdisj k
  have hSL := splitPoly_isSimple_of_diagonal P hS h2 i j hdiagD
  have hSR := splitPoly_isSimple_of_diagonal P hS h2 j i hdiag'
  obtain ⟨⟨pL, hpLL, hpLP, hpLwL, hpLwR⟩, ⟨pR, hpRR, hpRP, hpRwR, hpRwL⟩⟩ :=
    exists_split_separation_witness P hS hO h2 i j hdiagD hconv hwT
  exact splitPoly_positivelyOriented_of_witnesses P hS hO i j hij hSL hSR
    pL hpLL hpLP hpLwL hpLwR pR hpRR hpRP hpRwR hpRwL

/-- **Open corner triangle of an ear has winding `1`** (rotation bridge). For a simple
positively-oriented `L` with `L.n = m + 2`, `m ≥ 2`, and an ear vertex `i`, any point `q`
strictly inside the corner triangle `(vᵢ₋₁, vᵢ, vᵢ₊₁)` (the three open half-plane tests, in
`openEar` form) has `L.winding q = 1`. Proof: rotate `L` so that `i` lands at the standard
ear apex `m+1` (taking `c = i + 1`); the rotated open ear is exactly this open triangle, and
`winding_one_on_open_ear` for the rotation gives the result via `rotateP_winding`. -/
lemma openCorner_winding_one (L : LatticePolygon) (hSL : L.IsSimple)
    (hOL : L.PositivelyOriented) (m : ℕ) (hm : L.n = m + 2) (hm2 : 2 ≤ m)
    (i : ZMod L.n) (hear : isEarVertex L i) {q : ℝ × ℝ}
    (hq1 : 0 < cross (toReal (L.vert i) - toReal (L.vert (i - 1)))
              (q - toReal (L.vert (i - 1))))
    (hq2 : 0 < cross (toReal (L.vert (i + 1)) - toReal (L.vert i)) (q - toReal (L.vert i)))
    (hq3 : 0 < cross (toReal (L.vert (i - 1)) - toReal (L.vert (i + 1)))
              (q - toReal (L.vert (i + 1)))) :
    L.winding q = 1 := by
  set c : ZMod L.n := i + 1 with hc
  have hmz : (m : ZMod L.n) + 2 = 0 := by
    have h : ((m + 2 : ℕ) : ZMod L.n) = 0 := by rw [← hm]; exact ZMod.natCast_self L.n
    push_cast at h; linear_combination h
  -- the three rotated openEar vertices, as `L`-vertices
  have hvM : L.vert ((m : ZMod L.n) + c) = L.vert (i - 1) := by
    congr 1; rw [hc]; linear_combination hmz
  have hvA : L.vert (((m : ZMod L.n) + 1) + c) = L.vert i := by
    congr 1; rw [hc]; linear_combination hmz
  have hv0 : L.vert ((0 : ZMod L.n) + c) = L.vert (i + 1) := by
    congr 1; rw [hc]; ring
  -- ear at the rotated apex
  have hearL : isEarVertex L (((m : ZMod L.n) + 1) + c) := by
    have e : ((m : ZMod L.n) + 1) + c = i := by rw [hc]; linear_combination hmz
    rw [e]; exact hear
  have hearQ : isEarVertex (rotateP L c) ((m : ZMod (rotateP L c).n) + 1) := by
    rw [isEarVertex_rotateP]; exact hearL
  -- membership of `q` in the rotated open ear (each goal is defeq to its `ZMod L.n` form)
  have hmem : q ∈ openEar (rotateP L c) m := by
    refine ⟨?_, ?_, ?_⟩
    · show 0 < cross (toReal (L.vert (((m : ZMod L.n) + 1) + c)) - toReal (L.vert ((m : ZMod L.n) + c)))
        (q - toReal (L.vert ((m : ZMod L.n) + c)))
      rw [hvM, hvA]; exact hq1
    · show 0 < cross (toReal (L.vert ((0 : ZMod L.n) + c)) - toReal (L.vert (((m : ZMod L.n) + 1) + c)))
        (q - toReal (L.vert (((m : ZMod L.n) + 1) + c)))
      rw [hv0, hvA]; exact hq2
    · show 0 < cross (toReal (L.vert ((m : ZMod L.n) + c)) - toReal (L.vert ((0 : ZMod L.n) + c)))
        (q - toReal (L.vert ((0 : ZMod L.n) + c)))
      rw [hvM, hv0]; exact hq3
  have hw := winding_one_on_open_ear (rotateP L c) (isSimple_rotateP L c hSL)
    (positivelyOriented_rotateP L c hOL) m hm hm2 hearQ q hmem
  rwa [rotateP_winding] at hw

/-! ### Step B base case — the triangle

For a positively-oriented triangle (`n = 3`) every corner is a strict left turn, and the
ear-emptiness clause is vacuous (the three neighbour indices exhaust `ZMod 3`). This gives the
base case of the two-ears induction: for any edge `e`, the vertex `e + 2` is an ear avoiding
both endpoints of `e`. -/

/-- Every corner of a positively-oriented triangle is convex (`0 < cornerCross`). -/
lemma cornerCross_pos_triangle (P : LatticePolygon) (hn : P.n = 3) (hO : P.PositivelyOriented)
    (k : ZMod P.n) : 0 < cornerCross P k := by
  have h := crossZ_vertex_pos P hn hO k
  rw [crossZ] at h
  rw [cornerCross_eq_neg_cross_neighbors, ← toReal_sub, ← toReal_sub, cross_toReal_int]
  have hZ : ((((P.vert (k - 1) - P.vert k).1 * (P.vert (k + 1) - P.vert k).2
        - (P.vert (k - 1) - P.vert k).2 * (P.vert (k + 1) - P.vert k).1 : ℤ)) : ℝ)
      = -(((P.vert (k + 1) - P.vert k).1 * (P.vert (k - 1) - P.vert k).2
        - (P.vert (k + 1) - P.vert k).2 * (P.vert (k - 1) - P.vert k).1 : ℤ) : ℝ) := by
    push_cast; ring
  rw [hZ, neg_neg]
  exact_mod_cast h

/-- Pure `ZMod 3` fact: the three neighbour indices exhaust the type. -/
lemma zmod3_nbhd : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i - 1 := by decide

/-- Pure `ZMod 3` fact: `a + 2` differs from both `a` and `a + 1`. -/
lemma zmod3_shift : ∀ a : ZMod 3, a + 2 ≠ a ∧ a + 2 ≠ a + 1 := by decide

/-- In a triangle, the three neighbour indices of any vertex exhaust `ZMod 3`. -/
lemma triangle_index_nbhd (P : LatticePolygon) (hn : P.n = 3) (i j : ZMod P.n) :
    j = i ∨ j = i + 1 ∨ j = i - 1 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_nbhd i j

/-- In a triangle, `a + 2` differs from both `a` and `a + 1`. -/
lemma triangle_shift_ne (P : LatticePolygon) (hn : P.n = 3) (a : ZMod P.n) :
    a + 2 ≠ a ∧ a + 2 ≠ a + 1 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_shift a

/-- In a triangle, the ear-emptiness clause holds vacuously: every `j` is one of the three
neighbour indices `i - 1, i, i + 1`. -/
lemma triangle_empty_corner (P : LatticePolygon) (hn : P.n = 3) (i j : ZMod P.n)
    (h1 : j ≠ i - 1) (h2 : j ≠ i) (h3 : j ≠ i + 1) : False := by
  rcases triangle_index_nbhd P hn i j with h | h | h
  · exact h2 h
  · exact h3 h
  · exact h1 h

/-- **Triangle base case of two-ears.** For a positively-oriented triangle and any edge `e`,
the opposite vertex `e + 2` is an ear avoiding both endpoints `e`, `e + 1` of `e`. -/
lemma triangle_ear_avoiding (P : LatticePolygon) (hn : P.n = 3) (hO : P.PositivelyOriented)
    (e : ZMod P.n) : ∃ i : ZMod P.n, isEarVertex P i ∧ i ≠ e ∧ i ≠ e + 1 := by
  exact ⟨e + 2, ⟨cornerCross_pos_triangle P hn hO _,
    fun j hj1 hj2 hj3 => (triangle_empty_corner P hn (e + 2) j hj1 hj2 hj3).elim⟩,
    (triangle_shift_ne P hn e).1, (triangle_shift_ne P hn e).2⟩

/-- **Open corner triangle of an interior arc-ear has winding `1`, uniformly in `L.n ≥ 3`.**
Like `openCorner_winding_one`, but phrased for an *interior* vertex `i` (`0 < i.val`,
`i.val + 1 < L.n`) and also covering the triangle base case `L.n = 3` (where the corner
triangle is all of `L` and `winding_eq_one_of_cross_pos_real` applies). -/
lemma openCorner_winding_one' (L : LatticePolygon) (hSL : L.IsSimple)
    (hOL : L.PositivelyOriented) (i : ZMod L.n) (hlo : 0 < i.val)
    (hhi : i.val + 1 < L.n) (hear : isEarVertex L i) {q : ℝ × ℝ}
    (hq1 : 0 < cross (toReal (L.vert i) - toReal (L.vert (i - 1)))
              (q - toReal (L.vert (i - 1))))
    (hq2 : 0 < cross (toReal (L.vert (i + 1)) - toReal (L.vert i)) (q - toReal (L.vert i)))
    (hq3 : 0 < cross (toReal (L.vert (i - 1)) - toReal (L.vert (i + 1)))
              (q - toReal (L.vert (i + 1)))) :
    L.winding q = 1 := by
  rcases lt_or_ge L.n 4 with h3 | h4
  · -- triangle base case
    have hn3 : L.n = 3 := by omega
    have e2 : (i - 1) + 1 = i := by ring
    have h3z : (3 : ZMod L.n) = 0 := by
      have h : ((3 : ℕ) : ZMod L.n) = 0 := by rw [← hn3]; exact ZMod.natCast_self L.n
      exact_mod_cast h
    have e1 : (i + 1) + 1 = i - 1 := by linear_combination h3z
    have h : ∀ j : ZMod L.n,
        0 < cross (toReal (L.vert j) - q) (toReal (L.vert (j + 1)) - q) := by
      intro j
      have hid : cross (toReal (L.vert j) - q) (toReal (L.vert (j + 1)) - q)
          = cross (toReal (L.vert (j + 1)) - toReal (L.vert j)) (q - toReal (L.vert j)) := by
        simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
      rw [hid]
      rcases triangle_index_nbhd L hn3 i j with hj | hj | hj
      · subst hj; exact hq2
      · subst hj; rw [e1]; exact hq3
      · subst hj; rw [e2]; exact hq1
    have c0 : 0 < cross (toReal (L.vert i) - q) (toReal (L.vert (i + 1)) - q) := h i
    have c1 : 0 < cross (toReal (L.vert (i + 1)) - q) (toReal (L.vert (i - 1)) - q) := by
      have := h (i + 1); rwa [e1] at this
    have c2 : 0 < cross (toReal (L.vert (i - 1)) - q) (toReal (L.vert i) - q) := by
      have := h (i - 1); rwa [e2] at this
    have hbelow := exists_vertex_below_real q (toReal (L.vert i)) (toReal (L.vert (i + 1)))
      (toReal (L.vert (i - 1))) c0 c1 c2
    have habove := exists_vertex_above_real q (toReal (L.vert i)) (toReal (L.vert (i + 1)))
      (toReal (L.vert (i - 1))) c0 c1 c2
    refine winding_eq_one_of_cross_pos_real L hn3 q h ?_ ?_
    · rcases hbelow with hb | hb | hb
      · exact ⟨i, hb.le⟩
      · exact ⟨i + 1, hb.le⟩
      · exact ⟨i - 1, hb.le⟩
    · rcases habove with hb | hb | hb
      · exact ⟨i, hb⟩
      · exact ⟨i + 1, hb⟩
      · exact ⟨i - 1, hb⟩
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, L.n = m + 2 := ⟨L.n - 2, by omega⟩
    have hm2 : 2 ≤ m := by omega
    exact openCorner_winding_one L hSL hOL m hm hm2 i hear hq1 hq2 hq3

/-- **Winding-`0` point arbitrarily close to a vertex.** If the edge `[vₑ, vₑ₊₁]` is
non-horizontal, then within every ball around `vₑ` there is an off-boundary point with
`P.winding = 0` (a point of the right tube of edge `e`, placed near the vertex by taking the
foot parameter `s` small). The winding value is pinned by the `edgeWind` jump across the
matched left/right pair, exactly as in `exists_foot_pair_windings`. -/
lemma exists_winding_zero_near_vertex (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (e : ZMod P.n) (hne : (toReal (P.vert e)).2 ≠ (toReal (P.vert (e + 1))).2)
    {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ × ℝ, dist g (toReal (P.vert e)) < r ∧ g ∉ P.boundary ∧ P.winding g = 0 := by
  classical
  set a := toReal (P.vert e) with ha
  set b := toReal (P.vert (e + 1)) with hb
  set D := ‖P.edgeDir e‖ with hD
  set Δ := |b.2 - a.2| with hΔ
  have hDnn : 0 ≤ D := norm_nonneg _
  have hΔpos : 0 < Δ := by rw [hΔ]; exact abs_pos.2 (sub_ne_zero.2 (fun h => hne h.symm))
  have hden : 0 < 2 * (D + Δ + 1) := by positivity
  set s := min (1/2) (r / (2 * (D + Δ + 1))) with hsdef
  have hspos : 0 < s := lt_min (by norm_num) (by positivity)
  have hslt1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hs : s ∈ Set.Ioo (0:ℝ) 1 := ⟨hspos, hslt1⟩
  have hε : (0:ℝ) < 1 := one_pos
  have hf2 : (P.foot e s).2 = (1 - s) * a.2 + s * b.2 := by
    rw [LatticePolygon.foot, ← ha, ← hb]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  set m := min a.2 b.2 with hm
  set M := max a.2 b.2 with hM
  have hmM : m < (P.foot e s).2 ∧ (P.foot e s).2 < M := by
    rw [hf2, hm, hM]
    rcases lt_or_gt_of_ne hne with hab | hab
    · rw [min_eq_left hab.le, max_eq_right hab.le]; constructor <;> nlinarith [hs.1, hs.2]
    · rw [min_eq_right hab.le, max_eq_left hab.le]; constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨hmlt, hMlt⟩ := hmM
  obtain ⟨ρ, hρ, hball⟩ := winding_sub_edge_const_near_foot P hS e hne hs
  set η := min ρ (min ((P.foot e s).2 - m) (M - (P.foot e s).2)) with hη
  have hηpos : 0 < η := lt_min hρ (lt_min (by linarith) (by linarith))
  have hηm : η ≤ (P.foot e s).2 - m := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηM : η ≤ M - (P.foot e s).2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hηρ : η ≤ ρ := min_le_left _ _
  set cap := P.capHeight e 1 s with hcap
  have hcappos : 0 < cap := capHeight_pos P hS e hε hs
  set t := min (cap / 2) (η / 2) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have htcap : t < cap := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htη : t < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have htη2 : t ≤ η / 2 := min_le_right _ _
  set pR := P.rectMap e (P.rightNormal e) (s, t) with hpRdef
  set pL := P.rectMap e (P.leftNormal e) (s, t) with hpLdef
  have hpRmem : pR ∈ P.rightRegion e 1 := ⟨(s, t), ⟨hs, htpos, htcap⟩, rfl⟩
  have hpLmem : pL ∈ P.leftRegion e 1 := ⟨(s, t), ⟨hs, htpos, htcap⟩, rfl⟩
  have hdR : dist pR (P.foot e s) = t := by
    rw [hpRdef, dist_rectMap_foot, rightNormal_unit P hS, mul_one, abs_of_pos htpos]
  have hdL : dist pL (P.foot e s) = t := by
    rw [hpLdef, dist_rectMap_foot, leftNormal_unit P hS, mul_one, abs_of_pos htpos]
  have habs : ∀ p : ℝ × ℝ, |p.2 - (P.foot e s).2| ≤ dist p (P.foot e s) := by
    intro p
    rw [show |p.2 - (P.foot e s).2| = dist p.2 (P.foot e s).2 from (Real.dist_eq _ _).symm,
      Prod.dist_eq]
    exact le_max_right _ _
  have hheight : ∀ p : ℝ × ℝ, dist p (P.foot e s) = t → m < p.2 ∧ p.2 < M := by
    intro p hp
    have h1 : |p.2 - (P.foot e s).2| < (P.foot e s).2 - m := by
      have := habs p; rw [hp] at this; linarith
    have h2 : |p.2 - (P.foot e s).2| < M - (P.foot e s).2 := by
      have := habs p; rw [hp] at this; linarith
    exact ⟨by linarith [(abs_lt.1 h1).1], by linarith [(abs_lt.1 h2).2]⟩
  obtain ⟨hpL2lo, hpL2hi⟩ := hheight pL hdL
  obtain ⟨hpR2lo, hpR2hi⟩ := hheight pR hdR
  have hed : P.edgeDir e = b - a := by rw [LatticePolygon.edgeDir, ← ha, ← hb]
  have hcrossL : 0 < cross (b - a) (pL - a) := by
    have := rectMap_left_cross_pos P hS e (s := s) (t := t) htpos
    rwa [hed, ← ha, ← hpLdef] at this
  have hcrossR : cross (b - a) (pR - a) < 0 := by
    have := rectMap_right_cross_neg P hS e (s := s) (t := t) htpos
    rwa [hed, ← ha, ← hpRdef] at this
  have hjump : edgeWind a b pL - edgeWind a b pR = 1 :=
    edgeWind_jump_one a b pL pR hne hpL2lo hpL2hi hpR2lo hpR2hi hcrossL hcrossR
  have hbL := hball pL (by rw [hdL]; linarith)
  have hbR := hball pR (by rw [hdR]; linarith)
  rw [← ha, ← hb] at hbL hbR
  have hwL : P.winding pL = 1 := leftRegion_winding_one P hS hO hε e hpLmem
  have hwR : P.winding pR = 0 := by
    have : P.winding pL - P.winding pR = edgeWind a b pL - edgeWind a b pR := by linarith
    rw [hjump, hwL] at this; linarith
  refine ⟨pR, ?_, rightRegion_subset_compl_boundary P hS e hpRmem, hwR⟩
  -- distance bound: `dist pR a ≤ t + s·D ≤ s·Δ/2 + s·D < r`.
  have hfv : dist (P.foot e s) a = s * D := by
    rw [dist_eq_norm, show P.foot e s - a = s • (P.edgeDir e) from by
          rw [LatticePolygon.foot, LatticePolygon.edgeDir, ← ha, ← hb]; module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hspos.le, hD]
  have hηsΔ : η ≤ s * Δ := by
    rcases lt_or_gt_of_ne hne with hab | hab
    · have e1 : (P.foot e s).2 - m = s * Δ := by
        rw [hf2, hm, min_eq_left hab.le, hΔ, abs_of_pos (sub_pos.2 hab)]; ring
      rw [← e1]; exact hηm
    · have e1 : M - (P.foot e s).2 = s * Δ := by
        rw [hf2, hM, max_eq_left hab.le, hΔ, abs_of_neg (sub_neg.2 hab)]; ring
      rw [← e1]; exact hηM
  have htΔ : t ≤ s * Δ / 2 := le_trans htη2 (by linarith [hηsΔ])
  have hle : s ≤ r / (2 * (D + Δ + 1)) := min_le_right _ _
  rw [le_div_iff₀ hden] at hle
  have hdistbound : dist pR a < r := by
    have htri : dist pR a ≤ dist pR (P.foot e s) + dist (P.foot e s) a := dist_triangle _ _ _
    rw [hdR, hfv] at htri
    nlinarith [htri, htΔ, hle, hspos, hDnn, hΔpos, mul_nonneg hspos.le hDnn,
      mul_pos hspos hΔpos]
  exact hdistbound

/-! ### Lifting an interior-arc ear of a split half back to the parent

For a diagonal `(a, b)` and the arc `L = splitPoly P a b`, an **interior** vertex `i` of `L`
(`0 < i.val` and `i.val + 1 < L.n`, i.e. `i` is neither diagonal endpoint) sits at the parent
index `c = a + i.val`, with the same three neighbours. Hence the corner data (`cornerCross`,
the corner triangle `inTriangle`) transfers verbatim between `L` at `i` and `P` at `c`. -/

/-- **Interior arc-vertex index correspondence.** For an interior vertex `i` of the arc
`L = splitPoly P a b` the previous/next indices map to `(a + i.val) ∓ 1`. -/
lemma splitPoly_interior_corner_idx (a b : ZMod P.n)
    (i : ZMod (splitPoly P a b).n) (hlo : 0 < i.val)
    (hhi : i.val + 1 < (splitPoly P a b).n) :
    a + (((i - 1).val : ℕ) : ZMod P.n) = (a + ((i.val : ℕ) : ZMod P.n)) - 1 ∧
    a + (((i + 1).val : ℕ) : ZMod P.n) = (a + ((i.val : ℕ) : ZMod P.n)) + 1 := by
  refine ⟨?_, ?_⟩
  · have hv : (i - 1).val = i.val - 1 := by
      have e : i - 1 = (((i.val - 1 : ℕ)) : ZMod (splitPoly P a b).n) := by
        rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_zmod_val]
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [hv, Nat.cast_sub (by omega), Nat.cast_one]; ring
  · have hv : (i + 1).val = i.val + 1 := by
      have e : i + 1 = (((i.val + 1 : ℕ)) : ZMod (splitPoly P a b).n) := by
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [hv]; push_cast; ring

/-- **Interior arc-vertex vertex correspondence.** The three vertices of `L = splitPoly P a b`
around an interior `i` equal the three `P`-vertices around `a + i.val`. -/
lemma splitPoly_interior_corner_vert (a b : ZMod P.n)
    (i : ZMod (splitPoly P a b).n) (hlo : 0 < i.val)
    (hhi : i.val + 1 < (splitPoly P a b).n) :
    (splitPoly P a b).vert (i - 1) = P.vert ((a + ((i.val : ℕ) : ZMod P.n)) - 1) ∧
    (splitPoly P a b).vert i = P.vert (a + ((i.val : ℕ) : ZMod P.n)) ∧
    (splitPoly P a b).vert (i + 1) = P.vert ((a + ((i.val : ℕ) : ZMod P.n)) + 1) := by
  obtain ⟨h1, h2⟩ := splitPoly_interior_corner_idx P a b i hlo hhi
  refine ⟨?_, ?_, ?_⟩
  · rw [splitPoly_vert, h1]
  · rw [splitPoly_vert]
  · rw [splitPoly_vert, h2]

/-- **`cornerCross` transfers** from an interior arc vertex to the parent vertex. -/
lemma cornerCross_splitPoly_interior (a b : ZMod P.n)
    (i : ZMod (splitPoly P a b).n) (hlo : 0 < i.val)
    (hhi : i.val + 1 < (splitPoly P a b).n) :
    cornerCross (splitPoly P a b) i = cornerCross P (a + ((i.val : ℕ) : ZMod P.n)) := by
  obtain ⟨e1, e2, e3⟩ := splitPoly_interior_corner_vert P a b i hlo hhi
  rw [cornerCross, cornerCross, e1, e2, e3]

/-- **The corner triangle transfers** from an interior arc vertex to the parent vertex. -/
lemma inTriangle_splitPoly_interior (a b : ZMod P.n)
    (i : ZMod (splitPoly P a b).n) (hlo : 0 < i.val)
    (hhi : i.val + 1 < (splitPoly P a b).n) (x : ℝ × ℝ) :
    inTriangle (toReal ((splitPoly P a b).vert (i - 1)))
        (toReal ((splitPoly P a b).vert i)) (toReal ((splitPoly P a b).vert (i + 1))) x ↔
    inTriangle (toReal (P.vert ((a + ((i.val : ℕ) : ZMod P.n)) - 1)))
        (toReal (P.vert (a + ((i.val : ℕ) : ZMod P.n))))
        (toReal (P.vert ((a + ((i.val : ℕ) : ZMod P.n)) + 1))) x := by
  obtain ⟨e1, e2, e3⟩ := splitPoly_interior_corner_vert P a b i hlo hhi
  rw [e1, e2, e3]

/-- **Winding-`1` point arbitrarily close to a vertex.** For a simple positively-oriented
polygon `Q` and any edge `e`, within every ball around the vertex `v_e` there is an
off-boundary point with `Q.winding = 1` — a point of the left region of edge `e` placed
near the vertex by taking the foot parameter `s` and offset `t` both small. No
non-horizontality is needed (unlike `exists_winding_zero_near_vertex`): the left region
carries winding `1` directly via `leftRegion_winding_one`. -/
lemma exists_winding_one_near_vertex (Q : LatticePolygon) (hS : Q.IsSimple)
    (hO : Q.PositivelyOriented) (e : ZMod Q.n) {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ × ℝ, dist g (toReal (Q.vert e)) < r ∧ g ∉ Q.boundary ∧ Q.winding g = 1 := by
  classical
  set a := toReal (Q.vert e) with ha
  set b := toReal (Q.vert (e + 1)) with hb
  set D := ‖Q.edgeDir e‖ with hD
  have hDnn : 0 ≤ D := norm_nonneg _
  set s := min (1/2) (r / (2 * (D + 1))) with hsdef
  have hspos : 0 < s := lt_min (by norm_num) (by positivity)
  have hslt1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hs : s ∈ Set.Ioo (0:ℝ) 1 := ⟨hspos, hslt1⟩
  have hε : (0:ℝ) < 1 := one_pos
  set cap := Q.capHeight e 1 s with hcap
  have hcappos : 0 < cap := capHeight_pos Q hS e hε hs
  set t := min (cap / 2) (r / 4) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have htcap : t < cap := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set g := Q.rectMap e (Q.leftNormal e) (s, t) with hgdef
  have hgmem : g ∈ Q.leftRegion e 1 := ⟨(s, t), ⟨hs, htpos, htcap⟩, rfl⟩
  have hgoff : g ∉ Q.boundary := leftRegion_notMem_boundary Q hS e hgmem
  have hgw : Q.winding g = 1 := leftRegion_winding_one Q hS hO hε e hgmem
  refine ⟨g, ?_, hgoff, hgw⟩
  have hgfoot : dist g (Q.foot e s) = t := by
    rw [hgdef, dist_rectMap_foot, leftNormal_unit Q hS, mul_one, abs_of_pos htpos]
  have hfv : dist (Q.foot e s) a = s * D := by
    rw [dist_eq_norm, show Q.foot e s - a = s • (Q.edgeDir e) from by
          rw [LatticePolygon.foot, LatticePolygon.edgeDir, ← ha, ← hb]; module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hspos.le, hD]
  have htri : dist g a ≤ dist g (Q.foot e s) + dist (Q.foot e s) a := dist_triangle _ _ _
  rw [hgfoot, hfv] at htri
  have hsle : s ≤ r / (2 * (D + 1)) := min_le_right _ _
  have hkey : s * D ≤ r / 2 := by
    have h1 : s * (D + 1) ≤ (r / (2 * (D + 1))) * (D + 1) :=
      mul_le_mul_of_nonneg_right hsle (by positivity)
    have h2 : (r / (2 * (D + 1))) * (D + 1) = r / 2 := by field_simp
    nlinarith [h1, h2, hspos, hDnn]
  have htr4 : t ≤ r / 4 := min_le_right _ _
  linarith

/-- **Lifting an interior arc-ear to a parent ear.** For a diagonal `(a, b)` with the
positive-orientation data (`hconv` at `a`, `hwT`), if `i` is an *interior* ear vertex of the
arc `L = splitPoly P a b` (`0 < i.val`, `i.val + 1 < L.n`) then the parent vertex
`a + i.val` is an ear vertex of `P`. Convexity transfers verbatim
(`cornerCross_splitPoly_interior`); for emptiness, an offending parent vertex `v_k` in the
closed corner triangle is either an `L`-arc vertex (contradicting `isEarVertex L i` via
`inTriangle_splitPoly_interior`) or an `R`-only vertex, in which case the double-winding
contradiction (`L.winding = 1` near `v_k` by local constancy off `L.boundary`, an `R`-inside
point near `v_k` with `R.winding = 1`, both nonzero on an open set) contradicts the a.e.
disjointness `splitPoly_hdisj_of_witnesses`. -/
lemma corner_triangle_subset_half (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (h2 : 2 ≤ P.n) (a b : ZMod P.n) (hdiag : IsDiagonal P a b)
    (hconv : 0 < cornerCross P a)
    (hwT : inTriangle (toReal (P.vert (a - 1))) (toReal (P.vert a)) (toReal (P.vert (a + 1)))
            (toReal (P.vert b)))
    (i : ZMod (splitPoly P a b).n) (hlo : 0 < i.val)
    (hhi : i.val + 1 < (splitPoly P a b).n) (hear : isEarVertex (splitPoly P a b) i) :
    isEarVertex P (a + ((i.val : ℕ) : ZMod P.n)) := by
  classical
  haveI : NeZero P.n := ⟨by omega⟩
  obtain ⟨hab, hab1, hba1, hdisjE⟩ := hdiag
  have hdiagD : IsDiagonal P a b := ⟨hab, hab1, hba1, hdisjE⟩
  have hdiag' : IsDiagonal P b a :=
    ⟨fun h => hab h.symm, hba1, hab1, fun k => by rw [openSegment_symm]; exact hdisjE k⟩
  have hSL : (splitPoly P a b).IsSimple := splitPoly_isSimple_of_diagonal P hS h2 a b hdiagD
  have hSR : (splitPoly P b a).IsSimple := splitPoly_isSimple_of_diagonal P hS h2 b a hdiag'
  obtain ⟨hOL, hOR⟩ := splitPoly_positivelyOriented P hS hO h2 a b hdiagD hconv hwT
  -- corner abbreviations
  set a' : ℝ × ℝ := toReal ((splitPoly P a b).vert (i - 1)) with ha'
  set b' : ℝ × ℝ := toReal ((splitPoly P a b).vert i) with hb'
  set c' : ℝ × ℝ := toReal ((splitPoly P a b).vert (i + 1)) with hc'
  have hcc : 0 < cornerCross (splitPoly P a b) i := hear.1
  have hKeq : cornerCross (splitPoly P a b) i = cross (b' - a') (c' - b') := rfl
  set U : Set (ℝ × ℝ) :=
    {x | 0 < cross (b' - a') (x - a') ∧ 0 < cross (c' - b') (x - b') ∧
      0 < cross (a' - c') (x - c')} with hUdef
  have hUwind : ∀ p ∈ U, (splitPoly P a b).winding p = 1 := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    exact openCorner_winding_one' (splitPoly P a b) hSL hOL i hlo hhi hear hp1 hp2 hp3
  set cen : ℝ × ℝ := (3:ℝ)⁻¹ • (a' + b' + c') with hcen
  have hcenU : cen ∈ U := by
    refine ⟨?_, ?_, ?_⟩
    · have h1 : cross (b' - a') (cen - a') = cornerCross (splitPoly P a b) i / 3 := by
        rw [hKeq, hcen]
        simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [h1]; linarith
    · have h1 : cross (c' - b') (cen - b') = cornerCross (splitPoly P a b) i / 3 := by
        rw [hKeq, hcen]
        simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [h1]; linarith
    · have h1 : cross (a' - c') (cen - c') = cornerCross (splitPoly P a b) i / 3 := by
        rw [hKeq, hcen]
        simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [h1]; linarith
  obtain ⟨hcen1, hcen2, hcen3⟩ := hcenU
  refine ⟨?_, ?_⟩
  · rw [← cornerCross_splitPoly_interior P a b i hlo hhi]; exact hear.1
  · set c : ZMod P.n := a + ((i.val : ℕ) : ZMod P.n) with hc
    intro j hj1 hj2 hj3 hjT
    set vk : ℝ × ℝ := toReal (P.vert j) with hvk
    have hjT_L : inTriangle a' b' c' vk :=
      (inTriangle_splitPoly_interior P a b i hlo hhi vk).mpr hjT
    obtain ⟨hv1, hv2, hv3⟩ := hjT_L
    -- interior index facts
    have hi1v : (i - 1).val = i.val - 1 := by
      have e : i - 1 = (((i.val - 1 : ℕ)) : ZMod (splitPoly P a b).n) := by
        rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_zmod_val]
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hi2v : (i + 1).val = i.val + 1 := by
      have e : i + 1 = (((i.val + 1 : ℕ)) : ZMod (splitPoly P a b).n) := by
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt hhi]
    by_cases hcase : (j - a).val ≤ (b - a).val
    · -- CASE A: `j` is an (splitPoly P a b)-arc vertex
      set t : ZMod (splitPoly P a b).n := (((j - a).val : ℕ) : ZMod (splitPoly P a b).n) with htdef
      have htval : t.val = (j - a).val := by
        rw [htdef, ZMod.val_natCast, Nat.mod_eq_of_lt (by simp only [splitPoly_n]; omega)]
      have hidx : a + (j - a) = j := by ring
      have hLvt : toReal ((splitPoly P a b).vert t) = vk := by
        rw [hvk, splitPoly_vert, htval, ZMod.natCast_zmod_val, hidx]
      have ht_i : t ≠ i := by
        intro h
        apply hj2
        have hval : (j - a).val = i.val := by rw [← htval, h]
        rw [hc, ← hval, ZMod.natCast_zmod_val]; ring
      have ht_i1 : t ≠ i + 1 := by
        intro h
        apply hj3
        have hval : (j - a).val = i.val + 1 := by rw [← htval, h, hi2v]
        have e1 : c + 1 = a + (((i.val + 1 : ℕ)) : ZMod P.n) := by rw [hc]; push_cast; ring
        rw [e1, ← hval, ZMod.natCast_zmod_val]; ring
      have ht_im1 : t ≠ i - 1 := by
        intro h
        apply hj1
        have hval : (j - a).val = i.val - 1 := by rw [← htval, h, hi1v]
        have e1 : c - 1 = a + (((i.val - 1 : ℕ)) : ZMod P.n) := by
          rw [hc, Nat.cast_sub (by omega), Nat.cast_one]; ring
        rw [e1, ← hval, ZMod.natCast_zmod_val]; ring
      have hcon : inTriangle a' b' c' (toReal ((splitPoly P a b).vert t)) := by rw [hLvt]; exact ⟨hv1, hv2, hv3⟩
      exact hear.2 t ht_im1 ht_i ht_i1 hcon
    · -- CASE B: `j` is an R-only vertex; the double-winding contradiction
      push Not at hcase
      -- separation witnesses + a.e. disjointness
      obtain ⟨⟨pL, hpLL, hpLP, hpLwL, hpLwR⟩, ⟨pR, hpRR, hpRP, hpRwR, hpRwL⟩⟩ :=
        exists_split_separation_witness P hS hO h2 a b hdiagD hconv hwT
      have hdisj := splitPoly_hdisj_of_witnesses P hS hO a b hab hSL hSR
        pL hpLL hpLP hpLwL hpLwR pR hpRR hpRP hpRwR hpRwL
      have hja : j ≠ a := by intro h; rw [h, sub_self, ZMod.val_zero] at hcase; omega
      have hjb : j ≠ b := by intro h; rw [h] at hcase; omega
      -- (a) `v_k ∉ (splitPoly P a b).boundary`
      have hvkL : vk ∉ (splitPoly P a b).boundary := by
        intro hmem
        rw [LatticePolygon.boundary, Set.mem_iUnion] at hmem
        obtain ⟨k, hk⟩ := hmem
        have hjne : ∀ m : ZMod P.n, (m - a).val ≤ (b - a).val → j ≠ m := by
          intro m hm heq'; rw [heq'] at hcase; omega
        rcases splitPoly_idx_dichotomy P a b k with hlt | heq
        · rw [splitPoly_edgeSeg_kept P a b k hlt, hvk] at hk
          have hpos_e : ((a + ((k.val : ℕ) : ZMod P.n)) - a).val ≤ (b - a).val := by
            rw [add_sub_cancel_left, ZMod.val_natCast,
              Nat.mod_eq_of_lt (lt_trans hlt (ZMod.val_lt _))]
            exact le_of_lt hlt
          have hpos_e1 : ((a + ((k.val : ℕ) : ZMod P.n) + 1) - a).val ≤ (b - a).val := by
            have he : a + ((k.val : ℕ) : ZMod P.n) + 1 - a = (((k.val + 1 : ℕ)) : ZMod P.n) := by
              push_cast; ring
            rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt (b - a); omega)]
            omega
          exact vert_notMem_edgeSeg P hS j (a + ((k.val : ℕ) : ZMod P.n))
            (Ne.symm (hjne _ hpos_e)) (fun he => (hjne _ hpos_e1) (by rw [he]; ring)) hk
        · rw [splitPoly_edgeSeg_diag P a b k heq, hvk] at hk
          have hvbne : toReal (P.vert j) ≠ toReal (P.vert b) :=
            fun he => hjb (vert_injective P hS (toReal_injective he))
          have hvane : toReal (P.vert j) ≠ toReal (P.vert a) :=
            fun he => hja (vert_injective P hS (toReal_injective he))
          have hopen : toReal (P.vert j) ∈
              openSegment ℝ (toReal (P.vert b)) (toReal (P.vert a)) :=
            mem_openSegment_of_ne_ends hk hvbne hvane
          rw [openSegment_symm] at hopen
          have hmemedge : toReal (P.vert j) ∈ P.edgeSeg j := by
            rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _
          exact Set.disjoint_left.mp (hdisjE j) hopen hmemedge
      -- (b) `(splitPoly P a b).winding v_k = 1`
      have hev0 : {q | (splitPoly P a b).winding q = (splitPoly P a b).winding vk} ∈ nhds vk :=
        winding_eventually_eq_full (splitPoly P a b) vk hvkL
      obtain ⟨ε0, hε0pos, hsub0⟩ := Metric.mem_nhds_iff.1 hev0
      have hball0 : ∀ x, dist x vk < ε0 → (splitPoly P a b).winding x = (splitPoly P a b).winding vk :=
        fun x hx => hsub0 (Metric.mem_ball.2 hx)
      set lam : ℝ := min (1/2) (ε0 / (2 * (dist cen vk + 1))) with hlam
      have hlampos : 0 < lam := lt_min (by norm_num) (by positivity)
      have hlamle : lam ≤ 1/2 := min_le_left _ _
      set p : ℝ × ℝ := lam • cen + (1 - lam) • vk with hp
      have hf1p : 0 < cross (b' - a') (p - a') := by
        have hid : cross (b' - a') (p - a')
            = lam * cross (b' - a') (cen - a') + (1 - lam) * cross (b' - a') (vk - a') := by
          rw [hp]; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
            Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        rw [hid]
        nlinarith [mul_pos hlampos hcen1, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hv1]
      have hf2p : 0 < cross (c' - b') (p - b') := by
        have hid : cross (c' - b') (p - b')
            = lam * cross (c' - b') (cen - b') + (1 - lam) * cross (c' - b') (vk - b') := by
          rw [hp]; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
            Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        rw [hid]
        nlinarith [mul_pos hlampos hcen2, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hv2]
      have hf3p : 0 < cross (a' - c') (p - c') := by
        have hid : cross (a' - c') (p - c')
            = lam * cross (a' - c') (cen - c') + (1 - lam) * cross (a' - c') (vk - c') := by
          rw [hp]; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
            Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        rw [hid]
        nlinarith [mul_pos hlampos hcen3, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hv3]
      have hpU : p ∈ U := ⟨hf1p, hf2p, hf3p⟩
      have hpw : (splitPoly P a b).winding p = 1 := hUwind p hpU
      have hpdist : dist p vk < ε0 := by
        have heq : dist p vk = lam * dist cen vk := by
          rw [hp, dist_eq_norm,
            show lam • cen + (1 - lam) • vk - vk = lam • (cen - vk) from by module,
            norm_smul, Real.norm_eq_abs, abs_of_pos hlampos, ← dist_eq_norm]
        rw [heq]
        have hle : lam ≤ ε0 / (2 * (dist cen vk + 1)) := min_le_right _ _
        have hden : 0 < 2 * (dist cen vk + 1) := by positivity
        have h2' : lam * (2 * (dist cen vk + 1)) ≤ ε0 := (le_div_iff₀ hden).1 hle
        nlinarith [h2', hlampos, dist_nonneg (x := cen) (y := vk)]
      have hLwvk : (splitPoly P a b).winding vk = 1 := by
        have h := hball0 p hpdist; rw [hpw] at h; exact h.symm
      have hball1 : ∀ x, dist x vk < ε0 → (splitPoly P a b).winding x = 1 := by
        intro x hx; have h := hball0 x hx; rw [hLwvk] at h; exact h
      have hDLpos : 0 < Metric.infDist vk (splitPoly P a b).boundary := by
        rw [← (boundary_isClosed (splitPoly P a b)).notMem_iff_infDist_pos (boundary_nonempty (splitPoly P a b))]; exact hvkL
      -- (c) an `R`-inside point `g` near `v_k`
      have hjbn : (j - b).val < (splitPoly P b a).n := by
        have hsum : (j - b) + (b - a) = j - a := by ring
        have hva : ((j - b) + (b - a)).val = ((j - b).val + (b - a).val) % P.n := ZMod.val_add _ _
        rw [hsum] at hva
        have hb1 : (b - a).val < P.n := ZMod.val_lt _
        have hb2 : (j - b).val < P.n := ZMod.val_lt _
        have hb3 : (j - a).val < P.n := ZMod.val_lt _
        have hnd : (b - a).val + (a - b).val = P.n := by
          have h := val_add_val_neg P.n (b - a) (sub_ne_zero.2 (Ne.symm hab)); rwa [neg_sub] at h
        have hdisjsum : (j - b).val + (b - a).val = (j - a).val ∨
            (j - b).val + (b - a).val = (j - a).val + P.n := by
          rcases Nat.lt_or_ge ((j - b).val + (b - a).val) P.n with hlt | hge
          · left; rw [hva, Nat.mod_eq_of_lt hlt]
          · right
            rw [hva, Nat.mod_eq_sub_mod hge,
              Nat.mod_eq_of_lt (by omega : (j - b).val + (b - a).val - P.n < P.n)]
            omega
        simp only [splitPoly_n]; omega
      set iR : ZMod (splitPoly P b a).n := (((j - b).val : ℕ) : ZMod (splitPoly P b a).n) with hiR
      have hiRval : iR.val = (j - b).val := by
        rw [hiR, ZMod.val_natCast, Nat.mod_eq_of_lt hjbn]
      have hRvk : toReal ((splitPoly P b a).vert iR) = vk := by
        rw [hvk, splitPoly_vert, hiRval, ZMod.natCast_zmod_val]
        have hbb : b + (j - b) = j := by ring
        rw [hbb]
      set smallr : ℝ := min ε0 (Metric.infDist vk (splitPoly P a b).boundary) with hsmallr
      have hsmallpos : 0 < smallr := lt_min hε0pos hDLpos
      obtain ⟨g, hgdist, hgRb, hgRw⟩ :=
        exists_winding_one_near_vertex (splitPoly P b a) hSR hOR iR (r := smallr) hsmallpos
      have hgvk : dist g vk < smallr := by rw [← hRvk]; exact hgdist
      have hgLw : (splitPoly P a b).winding g = 1 := hball1 g (lt_of_lt_of_le hgvk (min_le_left _ _))
      have hgLb : g ∉ (splitPoly P a b).boundary := by
        intro hmem
        have hle : Metric.infDist vk (splitPoly P a b).boundary ≤ dist vk g := Metric.infDist_le_dist_of_mem hmem
        rw [dist_comm] at hle
        exact absurd (lt_of_lt_of_le hgvk (min_le_right _ _)) (not_lt.2 hle)
      -- (d) both windings nonzero on an open nbhd of `g`
      have hevL : ∀ᶠ q in nhds g, (splitPoly P a b).winding q = (splitPoly P a b).winding g := winding_eventually_eq_full (splitPoly P a b) g hgLb
      have hevR : ∀ᶠ q in nhds g, (splitPoly P b a).winding q = (splitPoly P b a).winding g :=
        winding_eventually_eq_full (splitPoly P b a) g hgRb
      have hboth : {q | (splitPoly P a b).winding q ≠ 0 ∧ (splitPoly P b a).winding q ≠ 0} ∈ nhds g := by
        filter_upwards [hevL, hevR] with q hqL hqR
        rw [hgLw] at hqL; rw [hgRw] at hqR
        exact ⟨by rw [hqL]; norm_num, by rw [hqR]; norm_num⟩
      obtain ⟨V, hVsub, hVopen, hgV⟩ := _root_.mem_nhds_iff.1 hboth
      have hVpos : 0 < MeasureTheory.volume V :=
        hVopen.measure_pos (μ := MeasureTheory.volume) ⟨g, hgV⟩
      have hnull : MeasureTheory.volume
          {q | (splitPoly P a b).winding q ≠ 0 ∧ (splitPoly P b a).winding q ≠ 0} = 0 := by
        have h := MeasureTheory.ae_iff.1 hdisj; simpa only [not_not] using h
      have hmono := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hVsub
      rw [hnull] at hmono
      exact absurd hmono (not_le.2 hVpos)

/-- **Mirror of `corner_triangle_subset_half` for the reverse arc.** Same diagonal data
`(a, b)` (with convexity/witness at `a`), but lifts an interior ear of the *complementary*
arc `R = splitPoly P b a` to the parent vertex `b + i.val`. Both halves are positively
oriented from the single `(a, b)` witness, so the corner-winding argument runs on `R` with
the inside point taken from `L = splitPoly P a b`; the a.e. disjointness is the same. -/
lemma corner_triangle_subset_half_R (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (h2 : 2 ≤ P.n) (a b : ZMod P.n) (hdiag : IsDiagonal P a b)
    (hconv : 0 < cornerCross P a)
    (hwT : inTriangle (toReal (P.vert (a - 1))) (toReal (P.vert a)) (toReal (P.vert (a + 1)))
            (toReal (P.vert b)))
    (i : ZMod (splitPoly P b a).n) (hlo : 0 < i.val)
    (hhi : i.val + 1 < (splitPoly P b a).n) (hear : isEarVertex (splitPoly P b a) i) :
    isEarVertex P (b + ((i.val : ℕ) : ZMod P.n)) := by
  classical
  haveI : NeZero P.n := ⟨by omega⟩
  obtain ⟨hab, hab1, hba1, hdisjE⟩ := hdiag
  have hdiagD : IsDiagonal P a b := ⟨hab, hab1, hba1, hdisjE⟩
  have hdiag' : IsDiagonal P b a :=
    ⟨fun h => hab h.symm, hba1, hab1, fun k => by rw [openSegment_symm]; exact hdisjE k⟩
  obtain ⟨hba, hba1', hab1', hdisjE'⟩ := hdiag'
  have hdiag'' : IsDiagonal P b a := ⟨hba, hba1', hab1', hdisjE'⟩
  have hSL : (splitPoly P a b).IsSimple := splitPoly_isSimple_of_diagonal P hS h2 a b hdiagD
  have hSR : (splitPoly P b a).IsSimple := splitPoly_isSimple_of_diagonal P hS h2 b a hdiag''
  obtain ⟨hOL, hOR⟩ := splitPoly_positivelyOriented P hS hO h2 a b hdiagD hconv hwT
  -- corner abbreviations (on the reverse arc `R`)
  set a' : ℝ × ℝ := toReal ((splitPoly P b a).vert (i - 1)) with ha'
  set b' : ℝ × ℝ := toReal ((splitPoly P b a).vert i) with hb'
  set c' : ℝ × ℝ := toReal ((splitPoly P b a).vert (i + 1)) with hc'
  have hcc : 0 < cornerCross (splitPoly P b a) i := hear.1
  have hKeq : cornerCross (splitPoly P b a) i = cross (b' - a') (c' - b') := rfl
  set U : Set (ℝ × ℝ) :=
    {x | 0 < cross (b' - a') (x - a') ∧ 0 < cross (c' - b') (x - b') ∧
      0 < cross (a' - c') (x - c')} with hUdef
  have hUwind : ∀ p ∈ U, (splitPoly P b a).winding p = 1 := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    exact openCorner_winding_one' (splitPoly P b a) hSR hOR i hlo hhi hear hp1 hp2 hp3
  set cen : ℝ × ℝ := (3:ℝ)⁻¹ • (a' + b' + c') with hcen
  have hcenU : cen ∈ U := by
    refine ⟨?_, ?_, ?_⟩
    · have h1 : cross (b' - a') (cen - a') = cornerCross (splitPoly P b a) i / 3 := by
        rw [hKeq, hcen]
        simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [h1]; linarith
    · have h1 : cross (c' - b') (cen - b') = cornerCross (splitPoly P b a) i / 3 := by
        rw [hKeq, hcen]
        simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [h1]; linarith
    · have h1 : cross (a' - c') (cen - c') = cornerCross (splitPoly P b a) i / 3 := by
        rw [hKeq, hcen]
        simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [h1]; linarith
  obtain ⟨hcen1, hcen2, hcen3⟩ := hcenU
  refine ⟨?_, ?_⟩
  · rw [← cornerCross_splitPoly_interior P b a i hlo hhi]; exact hear.1
  · set c : ZMod P.n := b + ((i.val : ℕ) : ZMod P.n) with hc
    intro j hj1 hj2 hj3 hjT
    set vk : ℝ × ℝ := toReal (P.vert j) with hvk
    have hjT_R : inTriangle a' b' c' vk :=
      (inTriangle_splitPoly_interior P b a i hlo hhi vk).mpr hjT
    obtain ⟨hv1, hv2, hv3⟩ := hjT_R
    have hi1v : (i - 1).val = i.val - 1 := by
      have e : i - 1 = (((i.val - 1 : ℕ)) : ZMod (splitPoly P b a).n) := by
        rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_zmod_val]
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hi2v : (i + 1).val = i.val + 1 := by
      have e : i + 1 = (((i.val + 1 : ℕ)) : ZMod (splitPoly P b a).n) := by
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt hhi]
    by_cases hcase : (j - b).val ≤ (a - b).val
    · -- CASE A: `j` is a vertex of the reverse arc `R`
      set t : ZMod (splitPoly P b a).n := (((j - b).val : ℕ) : ZMod (splitPoly P b a).n) with htdef
      have htval : t.val = (j - b).val := by
        rw [htdef, ZMod.val_natCast, Nat.mod_eq_of_lt (by simp only [splitPoly_n]; omega)]
      have hidx : b + (j - b) = j := by ring
      have hRvt : toReal ((splitPoly P b a).vert t) = vk := by
        rw [hvk, splitPoly_vert, htval, ZMod.natCast_zmod_val, hidx]
      have ht_i : t ≠ i := by
        intro h
        apply hj2
        have hval : (j - b).val = i.val := by rw [← htval, h]
        rw [hc, ← hval, ZMod.natCast_zmod_val]; ring
      have ht_i1 : t ≠ i + 1 := by
        intro h
        apply hj3
        have hval : (j - b).val = i.val + 1 := by rw [← htval, h, hi2v]
        have e1 : c + 1 = b + (((i.val + 1 : ℕ)) : ZMod P.n) := by rw [hc]; push_cast; ring
        rw [e1, ← hval, ZMod.natCast_zmod_val]; ring
      have ht_im1 : t ≠ i - 1 := by
        intro h
        apply hj1
        have hval : (j - b).val = i.val - 1 := by rw [← htval, h, hi1v]
        have e1 : c - 1 = b + (((i.val - 1 : ℕ)) : ZMod P.n) := by
          rw [hc, Nat.cast_sub (by omega), Nat.cast_one]; ring
        rw [e1, ← hval, ZMod.natCast_zmod_val]; ring
      have hcon : inTriangle a' b' c' (toReal ((splitPoly P b a).vert t)) := by
        rw [hRvt]; exact ⟨hv1, hv2, hv3⟩
      exact hear.2 t ht_im1 ht_i ht_i1 hcon
    · -- CASE B: `j` is an `L`-only vertex; the double-winding contradiction
      push Not at hcase
      obtain ⟨⟨pL, hpLL, hpLP, hpLwL, hpLwR⟩, ⟨pR, hpRR, hpRP, hpRwR, hpRwL⟩⟩ :=
        exists_split_separation_witness P hS hO h2 a b hdiagD hconv hwT
      have hdisj := splitPoly_hdisj_of_witnesses P hS hO a b hab hSL hSR
        pL hpLL hpLP hpLwL hpLwR pR hpRR hpRP hpRwR hpRwL
      have hja : j ≠ a := by intro h; rw [h] at hcase; omega
      have hjb : j ≠ b := by intro h; rw [h, sub_self, ZMod.val_zero] at hcase; omega
      -- (a) `v_k ∉ (splitPoly P b a).boundary`
      have hvkR : vk ∉ (splitPoly P b a).boundary := by
        intro hmem
        rw [LatticePolygon.boundary, Set.mem_iUnion] at hmem
        obtain ⟨k, hk⟩ := hmem
        have hjne : ∀ m : ZMod P.n, (m - b).val ≤ (a - b).val → j ≠ m := by
          intro m hm heq'; rw [heq'] at hcase; omega
        rcases splitPoly_idx_dichotomy P b a k with hlt | heq
        · rw [splitPoly_edgeSeg_kept P b a k hlt, hvk] at hk
          have hpos_e : ((b + ((k.val : ℕ) : ZMod P.n)) - b).val ≤ (a - b).val := by
            rw [add_sub_cancel_left, ZMod.val_natCast,
              Nat.mod_eq_of_lt (lt_trans hlt (ZMod.val_lt _))]
            exact le_of_lt hlt
          have hpos_e1 : ((b + ((k.val : ℕ) : ZMod P.n) + 1) - b).val ≤ (a - b).val := by
            have he : b + ((k.val : ℕ) : ZMod P.n) + 1 - b = (((k.val + 1 : ℕ)) : ZMod P.n) := by
              push_cast; ring
            rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt (a - b); omega)]
            omega
          exact vert_notMem_edgeSeg P hS j (b + ((k.val : ℕ) : ZMod P.n))
            (Ne.symm (hjne _ hpos_e)) (fun he => (hjne _ hpos_e1) (by rw [he]; ring)) hk
        · rw [splitPoly_edgeSeg_diag P b a k heq, hvk] at hk
          have hvane : toReal (P.vert j) ≠ toReal (P.vert a) :=
            fun he => hja (vert_injective P hS (toReal_injective he))
          have hvbne : toReal (P.vert j) ≠ toReal (P.vert b) :=
            fun he => hjb (vert_injective P hS (toReal_injective he))
          have hopen : toReal (P.vert j) ∈
              openSegment ℝ (toReal (P.vert a)) (toReal (P.vert b)) :=
            mem_openSegment_of_ne_ends hk hvane hvbne
          rw [openSegment_symm] at hopen
          have hmemedge : toReal (P.vert j) ∈ P.edgeSeg j := by
            rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _
          exact Set.disjoint_left.mp (hdisjE' j) hopen hmemedge
      -- (b) `(splitPoly P b a).winding v_k = 1`
      have hev0 : {q | (splitPoly P b a).winding q = (splitPoly P b a).winding vk} ∈ nhds vk :=
        winding_eventually_eq_full (splitPoly P b a) vk hvkR
      obtain ⟨ε0, hε0pos, hsub0⟩ := Metric.mem_nhds_iff.1 hev0
      have hball0 : ∀ x, dist x vk < ε0 → (splitPoly P b a).winding x = (splitPoly P b a).winding vk :=
        fun x hx => hsub0 (Metric.mem_ball.2 hx)
      set lam : ℝ := min (1/2) (ε0 / (2 * (dist cen vk + 1))) with hlam
      have hlampos : 0 < lam := lt_min (by norm_num) (by positivity)
      have hlamle : lam ≤ 1/2 := min_le_left _ _
      set p : ℝ × ℝ := lam • cen + (1 - lam) • vk with hp
      have hf1p : 0 < cross (b' - a') (p - a') := by
        have hid : cross (b' - a') (p - a')
            = lam * cross (b' - a') (cen - a') + (1 - lam) * cross (b' - a') (vk - a') := by
          rw [hp]; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
            Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        rw [hid]
        nlinarith [mul_pos hlampos hcen1, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hv1]
      have hf2p : 0 < cross (c' - b') (p - b') := by
        have hid : cross (c' - b') (p - b')
            = lam * cross (c' - b') (cen - b') + (1 - lam) * cross (c' - b') (vk - b') := by
          rw [hp]; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
            Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        rw [hid]
        nlinarith [mul_pos hlampos hcen2, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hv2]
      have hf3p : 0 < cross (a' - c') (p - c') := by
        have hid : cross (a' - c') (p - c')
            = lam * cross (a' - c') (cen - c') + (1 - lam) * cross (a' - c') (vk - c') := by
          rw [hp]; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
            Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        rw [hid]
        nlinarith [mul_pos hlampos hcen3, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hv3]
      have hpU : p ∈ U := ⟨hf1p, hf2p, hf3p⟩
      have hpw : (splitPoly P b a).winding p = 1 := hUwind p hpU
      have hpdist : dist p vk < ε0 := by
        have heq : dist p vk = lam * dist cen vk := by
          rw [hp, dist_eq_norm,
            show lam • cen + (1 - lam) • vk - vk = lam • (cen - vk) from by module,
            norm_smul, Real.norm_eq_abs, abs_of_pos hlampos, ← dist_eq_norm]
        rw [heq]
        have hle : lam ≤ ε0 / (2 * (dist cen vk + 1)) := min_le_right _ _
        have hden : 0 < 2 * (dist cen vk + 1) := by positivity
        have h2' : lam * (2 * (dist cen vk + 1)) ≤ ε0 := (le_div_iff₀ hden).1 hle
        nlinarith [h2', hlampos, dist_nonneg (x := cen) (y := vk)]
      have hRwvk : (splitPoly P b a).winding vk = 1 := by
        have h := hball0 p hpdist; rw [hpw] at h; exact h.symm
      have hball1 : ∀ x, dist x vk < ε0 → (splitPoly P b a).winding x = 1 := by
        intro x hx; have h := hball0 x hx; rw [hRwvk] at h; exact h
      have hDRpos : 0 < Metric.infDist vk (splitPoly P b a).boundary := by
        rw [← (boundary_isClosed (splitPoly P b a)).notMem_iff_infDist_pos
          (boundary_nonempty (splitPoly P b a))]; exact hvkR
      -- (c) an `L`-inside point `g` near `v_k`
      have hjan : (j - a).val < (splitPoly P a b).n := by
        have hsum : (j - a) + (a - b) = j - b := by ring
        have hva : ((j - a) + (a - b)).val = ((j - a).val + (a - b).val) % P.n := ZMod.val_add _ _
        rw [hsum] at hva
        have hb1 : (a - b).val < P.n := ZMod.val_lt _
        have hb2 : (j - a).val < P.n := ZMod.val_lt _
        have hb3 : (j - b).val < P.n := ZMod.val_lt _
        have hnd : (a - b).val + (b - a).val = P.n := by
          have h := val_add_val_neg P.n (a - b) (sub_ne_zero.2 (Ne.symm hba)); rwa [neg_sub] at h
        have hdisjsum : (j - a).val + (a - b).val = (j - b).val ∨
            (j - a).val + (a - b).val = (j - b).val + P.n := by
          rcases Nat.lt_or_ge ((j - a).val + (a - b).val) P.n with hlt | hge
          · left; rw [hva, Nat.mod_eq_of_lt hlt]
          · right
            rw [hva, Nat.mod_eq_sub_mod hge,
              Nat.mod_eq_of_lt (by omega : (j - a).val + (a - b).val - P.n < P.n)]
            omega
        simp only [splitPoly_n]; omega
      set iL : ZMod (splitPoly P a b).n := (((j - a).val : ℕ) : ZMod (splitPoly P a b).n) with hiL
      have hiLval : iL.val = (j - a).val := by
        rw [hiL, ZMod.val_natCast, Nat.mod_eq_of_lt hjan]
      have hLvk : toReal ((splitPoly P a b).vert iL) = vk := by
        rw [hvk, splitPoly_vert, hiLval, ZMod.natCast_zmod_val]
        have haa : a + (j - a) = j := by ring
        rw [haa]
      set smallr : ℝ := min ε0 (Metric.infDist vk (splitPoly P b a).boundary) with hsmallr
      have hsmallpos : 0 < smallr := lt_min hε0pos hDRpos
      obtain ⟨g, hgdist, hgLb, hgLw⟩ :=
        exists_winding_one_near_vertex (splitPoly P a b) hSL hOL iL (r := smallr) hsmallpos
      have hgvk : dist g vk < smallr := by rw [← hLvk]; exact hgdist
      have hgRw : (splitPoly P b a).winding g = 1 := hball1 g (lt_of_lt_of_le hgvk (min_le_left _ _))
      have hgRb : g ∉ (splitPoly P b a).boundary := by
        intro hmem
        have hle : Metric.infDist vk (splitPoly P b a).boundary ≤ dist vk g :=
          Metric.infDist_le_dist_of_mem hmem
        rw [dist_comm] at hle
        exact absurd (lt_of_lt_of_le hgvk (min_le_right _ _)) (not_lt.2 hle)
      -- (d) both windings nonzero on an open nbhd of `g`
      have hevL : ∀ᶠ q in nhds g, (splitPoly P a b).winding q = (splitPoly P a b).winding g :=
        winding_eventually_eq_full (splitPoly P a b) g hgLb
      have hevR : ∀ᶠ q in nhds g, (splitPoly P b a).winding q = (splitPoly P b a).winding g :=
        winding_eventually_eq_full (splitPoly P b a) g hgRb
      have hboth : {q | (splitPoly P a b).winding q ≠ 0 ∧ (splitPoly P b a).winding q ≠ 0} ∈ nhds g := by
        filter_upwards [hevL, hevR] with q hqL hqR
        rw [hgLw] at hqL; rw [hgRw] at hqR
        exact ⟨by rw [hqL]; norm_num, by rw [hqR]; norm_num⟩
      obtain ⟨V, hVsub, hVopen, hgV⟩ := _root_.mem_nhds_iff.1 hboth
      have hVpos : 0 < MeasureTheory.volume V :=
        hVopen.measure_pos (μ := MeasureTheory.volume) ⟨g, hgV⟩
      have hnull : MeasureTheory.volume
          {q | (splitPoly P a b).winding q ≠ 0 ∧ (splitPoly P b a).winding q ≠ 0} = 0 := by
        have h := MeasureTheory.ae_iff.1 hdisj; simpa only [not_not] using h
      have hmono := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hVsub
      rw [hnull] at hmono
      exact absurd hmono (not_le.2 hVpos)

/-- **Ear/diagonal dichotomy anchored at a given convex vertex `w`.** Either `w` is already an
ear, or its corner triangle's deepest contained vertex `v` spans a diagonal `[w, v]`. Unlike
`exists_ear_or_deepestContained`, the convex vertex is supplied (so the resulting ear/diagonal
is anchored at `w`, which the induction needs to dodge a prescribed edge). -/
lemma exists_ear_or_diagonal_at (hS : P.IsSimple) (w : ZMod P.n) (hconv : 0 < cornerCross P w) :
    isEarVertex P w ∨
    (∃ v : ZMod P.n, IsDiagonal P w v ∧ 0 < cornerCross P w ∧
      inTriangle (toReal (P.vert (w - 1))) (toReal (P.vert w)) (toReal (P.vert (w + 1)))
        (toReal (P.vert v))) := by
  classical
  by_cases hemp : ∃ j : ZMod P.n, j ≠ w - 1 ∧ j ≠ w ∧ j ≠ w + 1 ∧
      inTriangle (toReal (P.vert (w - 1))) (toReal (P.vert w)) (toReal (P.vert (w + 1)))
        (toReal (P.vert j))
  · right
    obtain ⟨v, hv, hvmax⟩ := exists_deepest_contained P w hemp
    exact ⟨v, deepest_contained_isDiagonal P hS w v hconv hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hvmax,
      hconv, hv.2.2.2⟩
  · left
    push Not at hemp
    exact isEarVertex_of_empty P w hconv hemp

/-- **Interiority from edge-avoidance.** An index `i` of `ZMod m` (`m ≥ 1`) that avoids both
`m − 1` and `(m − 1) + 1 = 0` is strictly interior: `0 < i.val` and `i.val + 1 < m`. Used to
turn the recursive ear (made to dodge the diagonal edge of a half) into an *interior* ear,
liftable through `corner_triangle_subset_half`. -/
private lemma interior_of_avoiding {m : ℕ} (i : ZMod m) (h1 : 1 ≤ m)
    (ha : i ≠ ((m - 1 : ℕ) : ZMod m)) (hb : i ≠ ((m - 1 : ℕ) : ZMod m) + 1) :
    0 < i.val ∧ i.val + 1 < m := by
  haveI : NeZero m := ⟨by omega⟩
  have heHsucc : (((m - 1 : ℕ) : ZMod m) + 1) = 0 := by
    have hcc : ((m - 1 : ℕ) : ZMod m) + 1 = ((m - 1 + 1 : ℕ) : ZMod m) := by push_cast; ring
    rw [hcc, show m - 1 + 1 = m from by omega, ZMod.natCast_self]
  have hi0 : i ≠ 0 := heHsucc ▸ hb
  have hlo : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi0 ((ZMod.val_eq_zero i).mp h))
  have hiHne : i.val ≠ m - 1 := by
    intro h; apply ha; rw [← ZMod.natCast_zmod_val i, h]
  have := ZMod.val_lt i
  exact ⟨hlo, by omega⟩

/-- **Two-ears induction (edge-avoiding form).** Every simple, positively-oriented lattice
polygon with `≥ 3` vertices has an ear vertex avoiding both endpoints of any prescribed edge `e`.
Strong induction on `n`: the triangle base is `triangle_ear_avoiding`; for `n ≥ 4` a convex vertex
`w ∉ {e, e+1}` either is itself an ear, or spans a diagonal `[w, v]` whose two arcs split off a
strictly smaller polygon.  The edge `e` lies in (the closure of) exactly one arc, so recursing on
the *other* half — at its diagonal edge, forcing an interior ear via `interior_of_avoiding` —
produces an ear lifting (`corner_triangle_subset_half`/`_R`) to a `P`-ear off `e`. -/
lemma ear_avoiding : ∀ (n : ℕ) (P : LatticePolygon), P.IsSimple → P.PositivelyOriented →
    P.n = n → 3 ≤ n → ∀ e : ZMod P.n, ∃ i : ZMod P.n, isEarVertex P i ∧ i ≠ e ∧ i ≠ e + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro P hS hO hPn h3 e
    rcases eq_or_lt_of_le h3 with h3eq | h4
    · exact triangle_ear_avoiding P (by omega) hO e
    · have h2 : 2 ≤ P.n := by omega
      haveI : NeZero P.n := ⟨by omega⟩
      haveI : Fact (1 < P.n) := ⟨by omega⟩
      obtain ⟨w, hwconv, hwe, hwe1⟩ := exists_convex_vertex_avoiding P hS hO (by omega) e (e + 1)
      rcases exists_ear_or_diagonal_at P hS w hwconv with hear | ⟨v, hdiag, _, hwT⟩
      · exact ⟨w, hear, hwe, hwe1⟩
      · -- diagonal `(w, v)`: split and recurse on the half away from `e`
        have hwv := hdiag.1
        have hwv1 := hdiag.2.1
        have hvw1 := hdiag.2.2.1
        have hdiag' : IsDiagonal P v w :=
          ⟨fun h => hwv h.symm, hvw1, hwv1, fun k => by
            rw [openSegment_symm]; exact hdiag.2.2.2 k⟩
        have hSL : (splitPoly P w v).IsSimple := splitPoly_isSimple_of_diagonal P hS h2 w v hdiag
        have hSR : (splitPoly P v w).IsSimple := splitPoly_isSimple_of_diagonal P hS h2 v w hdiag'
        obtain ⟨hOL, hOR⟩ := splitPoly_positivelyOriented P hS hO h2 w v hdiag hwconv hwT
        have hnL3 : 3 ≤ (splitPoly P w v).n := three_le_splitPoly_n P h2 w v hwv hwv1
        have hnLlt : (splitPoly P w v).n < n := hPn ▸ splitPoly_n_lt P h2 w v hwv hvw1
        have hnR3 : 3 ≤ (splitPoly P v w).n := three_le_splitPoly_n P h2 v w (fun h => hwv h.symm) hvw1
        have hnRlt : (splitPoly P v w).n < n := hPn ▸ splitPoly_n_lt P h2 v w (fun h => hwv h.symm) hwv1
        -- common arithmetic facts about positions `(· − w).val`
        have hwv0 : v - w ≠ 0 := sub_ne_zero.2 (fun h => hwv h.symm)
        have hsum : (v - w).val + (w - v).val = P.n := by
          have h := val_add_val_neg P.n (v - w) hwv0
          rwa [show -(v - w) = w - v from by ring] at h
        have hdvwpos : 1 ≤ (v - w).val := by
          rw [Nat.one_le_iff_ne_zero]; intro h; exact hwv0 ((ZMod.val_eq_zero _).mp h)
        have hpe1eq : (e + 1 - w).val = (e - w).val + 1 := by
          have hpene : (e - w).val ≠ P.n - 1 := by
            intro h
            apply hwe1
            have hsucc0 : ((P.n - 1 : ℕ) : ZMod P.n) + 1 = 0 := by
              have hcc : ((P.n - 1 : ℕ) : ZMod P.n) + 1 = ((P.n - 1 + 1 : ℕ) : ZMod P.n) := by
                push_cast; ring
              rw [hcc, show P.n - 1 + 1 = P.n from by omega, ZMod.natCast_self]
            have hew : e - w = ((P.n - 1 : ℕ) : ZMod P.n) := by
              rw [← ZMod.natCast_zmod_val (e - w), h]
            have hez : (e - w) + 1 = 0 := by rw [hew]; exact hsucc0
            linear_combination -hez
          rw [show e + 1 - w = (e - w) + 1 from by ring, ZMod.val_add, ZMod.val_one,
            Nat.mod_eq_of_lt (by have := ZMod.val_lt (e - w); omega)]
        by_cases hcase : (e - w).val < (v - w).val
        · -- edge `e` touches the `w→v` arc: recurse on the OTHER half `splitPoly P v w`
          obtain ⟨iR, hearR, hiRa, hiRb⟩ :=
            IH (splitPoly P v w).n hnRlt (splitPoly P v w) hSR hOR rfl hnR3
              (((splitPoly P v w).n - 1 : ℕ) : ZMod (splitPoly P v w).n)
          obtain ⟨hloR, hhiR⟩ := interior_of_avoiding iR (by omega) hiRa hiRb
          have hP_ear : isEarVertex P (v + ((iR.val : ℕ) : ZMod P.n)) :=
            corner_triangle_subset_half_R P hS hO h2 w v hdiag hwconv hwT iR hloR hhiR hearR
          have hRn : (splitPoly P v w).n = (w - v).val + 1 := rfl
          have hiRn : iR.val < P.n := by have := ZMod.val_lt iR; omega
          have hiRlt : iR.val < (w - v).val := by have := hhiR; omega
          have hsumlt : (v - w).val + iR.val < P.n := by omega
          have hposR : (v + ((iR.val : ℕ) : ZMod P.n) - w).val = (v - w).val + iR.val := by
            rw [show v + ((iR.val : ℕ) : ZMod P.n) - w = (v - w) + ((iR.val : ℕ) : ZMod P.n) from by
                ring, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hiRn,
              Nat.mod_eq_of_lt hsumlt]
          refine ⟨v + ((iR.val : ℕ) : ZMod P.n), hP_ear, ?_, ?_⟩
          · intro hc
            have h : (v + ((iR.val : ℕ) : ZMod P.n) - w).val = (e - w).val := by rw [hc]
            rw [hposR] at h
            omega
          · intro hc
            have h : (v + ((iR.val : ℕ) : ZMod P.n) - w).val = (e + 1 - w).val := by rw [hc]
            rw [hposR, hpe1eq] at h
            omega
        · -- edge `e` is in the `v→w` arc: recurse on `splitPoly P w v`
          push Not at hcase
          obtain ⟨iL, hearL, hiLa, hiLb⟩ :=
            IH (splitPoly P w v).n hnLlt (splitPoly P w v) hSL hOL rfl hnL3
              (((splitPoly P w v).n - 1 : ℕ) : ZMod (splitPoly P w v).n)
          obtain ⟨hloL, hhiL⟩ := interior_of_avoiding iL (by omega) hiLa hiLb
          have hP_ear : isEarVertex P (w + ((iL.val : ℕ) : ZMod P.n)) :=
            corner_triangle_subset_half P hS hO h2 w v hdiag hwconv hwT iL hloL hhiL hearL
          have hLn : (splitPoly P w v).n = (v - w).val + 1 := rfl
          have hiLn : iL.val < P.n := by have := ZMod.val_lt iL; omega
          have hposL : (w + ((iL.val : ℕ) : ZMod P.n) - w).val = iL.val := by
            rw [show w + ((iL.val : ℕ) : ZMod P.n) - w = ((iL.val : ℕ) : ZMod P.n) from by ring,
              ZMod.val_natCast, Nat.mod_eq_of_lt hiLn]
          refine ⟨w + ((iL.val : ℕ) : ZMod P.n), hP_ear, ?_, ?_⟩
          · intro hc
            have h : (w + ((iL.val : ℕ) : ZMod P.n) - w).val = (e - w).val := by rw [hc]
            rw [hposL] at h
            have := hhiL
            omega
          · intro hc
            have h : (w + ((iL.val : ℕ) : ZMod P.n) - w).val = (e + 1 - w).val := by rw [hc]
            rw [hposL, hpe1eq] at h
            have := hhiL
            omega

/-- **Existence of an ear** (O'Rourke / Meisters two-ears) for `n ≥ 4`: drop the edge-avoidance. -/
lemma exists_ear (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented)
    (h4 : 4 ≤ P.n) : ∃ i : ZMod P.n, isEarVertex P i := by
  obtain ⟨i, hi, _, _⟩ := ear_avoiding P.n P hS hO rfl (by omega) 0
  exact ⟨i, hi⟩

/-- **Pick's theorem** (Freek #92), final and self-contained: every simple,
positively-oriented lattice polygon has area `I + B/2 − 1`.  Combines the
ear-provider reduction with the just-proved existence of an ear (`exists_ear`,
the Meisters two-ears construction over the polygonal Jordan curve theorem).
This is the canonical statement (the `Defs.lean` placeholder was removed since
that file is upstream of this development). -/
theorem pick (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_provider (earProvider_of_exists_ear exists_ear) P hS hO

end JordanAtMostTwo

end Pick
