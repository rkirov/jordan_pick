import Submission.Pick.Corners

/-!
# Pick's theorem: line boundary, boundary arcs, parity spanning (Module 4)

The `LineBoundary`, `BoundaryArc`, and `ParitySpanning` sections. Lives inside
`namespace Pick`.
-/

namespace Pick

open LatticePolygon

variable (P : LatticePolygon)

/-! ### Boundary points on a generic horizontal line

A foundational geometric fact powering both the combinatorial and the continuous
routes to `winding_le_one`: at a *generic* height `y` (no endpoint of the edge is
at height `y`), a point `(x, y)` of the horizontal line `{·.2 = y}` lies on the
closed edge segment `[a, b]` **iff** the edge spans `y` and `x` is its crossing
threshold. In particular a boundary point at a generic height is exactly a
spanning-edge crossing, so the open horizontal gap between two threshold-adjacent
crossings is disjoint from the boundary (the input planarity needs to rule out
the same-sign / nesting configuration). -/

section LineBoundary

open LatticePolygon

variable (P : LatticePolygon)

/-- **A point of a generic horizontal line on an edge segment is the crossing
threshold of a spanning edge.** If `(x, y)` lies on the closed segment `[a, b]`
and neither endpoint sits at height `y`, then the edge spans `y` (its endpoints
straddle the line) and `x = crossThreshold a b y`. The single geometric atom for
reducing horizontal-line/boundary incidence to the finite spanning structure. -/
lemma eq_threshold_of_mem_segment_horizontal
    (a b : ℝ × ℝ) (y x : ℝ) (hy : y ≠ a.2) (hy' : y ≠ b.2)
    (hmem : (x, y) ∈ segment ℝ a b) :
    x = crossThreshold a b y ∧
      ((a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)) := by
  rw [segment_eq_image] at hmem
  obtain ⟨t, ht, hxy⟩ := hmem
  rw [Prod.ext_iff] at hxy
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
  obtain ⟨hx, hyt⟩ := hxy
  obtain ⟨ht0, ht1⟩ := ht
  -- hyt : (1 - t) * a.2 + t * b.2 = y ; hx : (1 - t) * a.1 + t * b.1 = x
  have hspan : (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) := by
    rcases lt_trichotomy a.2 b.2 with hab | hab | hab
    · left
      constructor
      · -- a.2 < y : since y is a convex combo with t>0 weight on larger b.2; need t ≠ 0
        rcases eq_or_lt_of_le ht0 with ht0' | ht0'
        · exfalso; apply hy; rw [← hyt, ← ht0']; ring
        · nlinarith [ht0', ht1, hab]
      · rcases eq_or_lt_of_le ht1 with ht1' | ht1'
        · exfalso; apply hy'; rw [← hyt, ht1']; ring
        · nlinarith [ht0, ht1', hab]
    · exfalso; apply hy; rw [← hyt, hab]; ring
    · right
      constructor
      · rcases eq_or_lt_of_le ht1 with ht1' | ht1'
        · exfalso; apply hy'; rw [← hyt, ht1']; ring
        · nlinarith [ht0, ht1', hab]
      · rcases eq_or_lt_of_le ht0 with ht0' | ht0'
        · exfalso; apply hy; rw [← hyt, ← ht0']; ring
        · nlinarith [ht0', ht1, hab]
  refine ⟨?_, hspan⟩
  -- now compute x = crossThreshold
  have hd : b.2 - a.2 ≠ 0 := by
    rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      · intro h; have := sub_eq_zero.mp h; linarith
  -- solve t = (y - a.2)/(b.2 - a.2) from hyt
  have ht_eq : t = (y - a.2) / (b.2 - a.2) := by
    field_simp
    nlinarith [hyt]
  rw [← hx, ht_eq, crossThreshold]
  field_simp
  ring

/-- **A boundary point at a generic height is a spanning-edge crossing.** At a
height `y` with no vertex on the line (`∀ i, (vert i).2 ≠ y`), every boundary point
`(x, y)` is the crossing threshold of some edge spanning `y`. Consequently a point
of the line is *off* the boundary as soon as it differs from every spanning
threshold. This converts the topological "horizontal line ∩ boundary" into the
finite spanning-threshold set — the bridge from `boundary` to `spanningSet`. -/
lemma exists_spanning_threshold_of_mem_boundary (y : ℝ)
    (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y) (x : ℝ)
    (hb : (x, y) ∈ P.boundary) :
    ∃ i ∈ P.spanningSet y, x = P.edgeThr y i := by
  classical
  simp only [LatticePolygon.boundary, LatticePolygon.edgeSeg, Set.mem_iUnion] at hb
  obtain ⟨i, hi⟩ := hb
  obtain ⟨hxeq, hspan⟩ :=
    eq_threshold_of_mem_segment_horizontal _ _ y x (hgen i).symm (hgen (i + 1)).symm hi
  refine ⟨i, ?_, hxeq⟩
  simp only [spanningSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hspan

/-- **The open horizontal gap between threshold-adjacent crossings is off the
boundary.** Fix a generic height `y`. If `x` lies strictly between two reals `x₁`,
`x₂` and *no* spanning edge has its crossing threshold in the closed range
`[x₁, x₂]` that `x` falls in — more precisely, if every spanning threshold is
either `≤ x₁` or `≥ x₂` — then `(x, y)` is not on the boundary. This is the precise
"chord interior is empty" planarity input: the winding is constant on the gap, and
the non-crossing argument forbids a same-sign pair of threshold-adjacent crossings
by examining this gap. -/
lemma notMem_boundary_of_between_thresholds (y : ℝ)
    (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y) (x x₁ x₂ : ℝ)
    (hx : x₁ < x ∧ x < x₂)
    (hgap : ∀ i ∈ P.spanningSet y, P.edgeThr y i ≤ x₁ ∨ x₂ ≤ P.edgeThr y i) :
    (x, y) ∉ P.boundary := by
  intro hb
  obtain ⟨i, hiSpan, hxeq⟩ := exists_spanning_threshold_of_mem_boundary P y hgen x hb
  rcases hgap i hiSpan with h | h
  · rw [hxeq] at hx; linarith [hx.1]
  · rw [hxeq] at hx; linarith [hx.2]

end LineBoundary

end Pick
