import JordanPick.PicksTheorem.Pick.Corners

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

/-! ### Boundary sub-arcs as connected sets

For the no-nesting (planarity) argument we need the polygon boundary, traversed
from one edge to another, as a *connected* set. The sub-arc `arcSet i d` is the
union of the `d+1` consecutive edge segments `edgeSeg i, …, edgeSeg (i+d)`. Since
consecutive edges share the vertex between them, the union is connected (a chain of
overlapping connected segments). This is the topological substrate for the
intermediate-value / Jordan crossing argument behind `threshold_consecutive_opposite`. -/

section BoundaryArc

open LatticePolygon

variable (P : LatticePolygon)

/-- The boundary **sub-arc** from edge `i` running forward `d` steps: the union of
the consecutive edge segments `edgeSeg i, edgeSeg (i+1), …, edgeSeg (i+d)`. -/
noncomputable def arcSet (i : ZMod P.n) (d : ℕ) : Set (ℝ × ℝ) :=
  ⋃ t ∈ Finset.range (d + 1), P.edgeSeg (i + (t : ZMod P.n))

/-- Each edge segment is connected (it is a segment, hence convex and nonempty). -/
lemma isConnected_edgeSeg (i : ZMod P.n) : IsConnected (P.edgeSeg i) := by
  rw [LatticePolygon.edgeSeg]
  exact (convex_segment _ _).isConnected ⟨_, left_mem_segment ℝ _ _⟩

/-- The crossing point `edgeSeg (i+1)` shares with `edgeSeg i` at the vertex `i+1`:
consecutive edge segments meet (their intersection is nonempty). -/
lemma edgeSeg_inter_succ_nonempty (i : ZMod P.n) :
    (P.edgeSeg i ∩ P.edgeSeg (i + 1)).Nonempty :=
  ⟨toReal (P.vert (i + 1)),
    by rw [LatticePolygon.edgeSeg]; exact right_mem_segment ℝ _ _,
    by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩

/-- **A boundary sub-arc is connected.** The union of `d+1` consecutive edge
segments is connected: each is connected and each meets the next at their shared
vertex, so the chain `⋃ edgeSeg (i+t)` is connected by induction. -/
lemma isConnected_arcSet (i : ZMod P.n) (d : ℕ) : IsConnected (arcSet P i d) := by
  unfold arcSet
  induction d with
  | zero =>
    have hr : (⋃ t ∈ Finset.range (0 + 1), P.edgeSeg (i + (t : ZMod P.n))) = P.edgeSeg i := by simp
    rw [hr]; exact isConnected_edgeSeg P i
  | succ d IH =>
    have hsplit : (⋃ t ∈ Finset.range (d + 1 + 1), P.edgeSeg (i + (t : ZMod P.n)))
        = (⋃ t ∈ Finset.range (d + 1), P.edgeSeg (i + (t : ZMod P.n)))
          ∪ P.edgeSeg (i + ((d + 1 : ℕ) : ZMod P.n)) := by
      rw [Finset.range_add_one]; simp [Set.biUnion_insert, Set.union_comm]
    rw [hsplit]
    refine IH.union ?_ (isConnected_edgeSeg P _)
    -- the running union (containing edge `i+d`) meets the new edge `i+(d+1)` at vertex `i+(d+1)`
    refine ⟨toReal (P.vert (i + ((d + 1 : ℕ) : ZMod P.n))), ?_, ?_⟩
    · rw [Set.mem_iUnion₂]
      refine ⟨d, by simp, ?_⟩
      rw [LatticePolygon.edgeSeg,
        show (i + ((d : ℕ) : ZMod P.n)) + 1 = i + ((d + 1 : ℕ) : ZMod P.n) by push_cast; ring]
      exact right_mem_segment ℝ _ _
    · rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _

/-- The sub-arc is contained in the polygon boundary. -/
lemma arcSet_subset_boundary (i : ZMod P.n) (d : ℕ) : arcSet P i d ⊆ P.boundary := by
  unfold arcSet boundary
  intro p hp
  rw [Set.mem_iUnion₂] at hp
  obtain ⟨t, _, hpt⟩ := hp
  exact Set.mem_iUnion.mpr ⟨i + (t : ZMod P.n), hpt⟩

/-- Each constituent edge segment of the sub-arc lies in the sub-arc. -/
lemma edgeSeg_subset_arcSet (i : ZMod P.n) (d : ℕ) (t : ℕ) (ht : t ≤ d) :
    P.edgeSeg (i + (t : ZMod P.n)) ⊆ arcSet P i d := by
  unfold arcSet
  intro p hp
  rw [Set.mem_iUnion₂]
  exact ⟨t, Finset.mem_range.mpr (by omega), hp⟩

end BoundaryArc

/-! ### Parity: equal-sign spanning edges are not cyclically adjacent

The curve-order alternation `edgeSign_consecutive_opposite` says cyclically
consecutive spanning edges carry opposite signs. Contrapositively, two spanning
edges with the *same* sign cannot be cyclically consecutive: there must be a
spanning edge strictly between them in cyclic vertex order. This is the purely
combinatorial parity input that, combined with the threshold-consecutiveness of
the pair (which forces the in-between spanning edge's threshold *outside* the
open threshold interval), sets up the no-nesting contradiction for
`threshold_consecutive_opposite`. -/

section ParitySpanning

open LatticePolygon

variable (P : LatticePolygon)

/-- **Equal-sign spanning edges have a spanning edge strictly between them.** If
`i` and `i+d` (`d ≥ 1`) both span the generic height `y` and carry the *same*
`edgeSign`, then some intermediate edge `i+t` (`1 ≤ t < d`) also spans `y`. (Were
there none, `edgeSign_consecutive_opposite` would force opposite signs.) -/
lemma exists_spanning_strictly_between_of_eq_sign (y : ℝ)
    (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : i ∈ P.spanningSet y) (hspj : i + (d : ZMod P.n) ∈ P.spanningSet y)
    (hsame : P.edgeSign y i = P.edgeSign y (i + (d : ZMod P.n))) :
    ∃ t : ℕ, 1 ≤ t ∧ t < d ∧ (i + (t : ZMod P.n)) ∈ P.spanningSet y := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hmid : ∀ t : ℕ, 1 ≤ t → t < d → (i + (t : ZMod P.n)) ∉ P.spanningSet y :=
    fun t ht1 ht2 => hcon t ht1 ht2
  have hopp := edgeSign_consecutive_opposite P y hy i d hd hspi hspj hmid
  rw [hsame] at hopp
  rcases edgeSign_eq_one_or_neg_one P y (i + (d : ZMod P.n)) with h | h <;>
    rw [h] at hopp <;> norm_num at hopp

/-- **Adjacent-opposite chain ⟹ `Alternates`.** A list of integers whose every
*adjacent* pair is sign-opposite (`b = -a`) is an `Alternates` list. This is the
purely list-combinatorial repackaging that turns the geometric
"threshold-consecutive spanning edges have opposite signs" statement into the
`Alternates (L.map edgeSign)` hypothesis consumed by the winding-bound pipeline. -/
lemma alternates_of_chain_neg : ∀ (S : List ℤ),
    S.IsChain (fun a b => b = -a) → AlternationCore.Alternates S := by
  intro S
  induction S with
  | nil => intro _; trivial
  | cons a t IH =>
    cases t with
    | nil => intro _; trivial
    | cons b s =>
      intro hadj
      rw [List.isChain_cons_cons] at hadj
      exact ⟨hadj.1, IH hadj.2⟩

/-- **Packaging: threshold-consecutive-opposite ⟹ x-sorted alternation.** If `L`
enumerates the spanning edges in *strictly threshold-increasing* order and every
threshold-*adjacent* pair in `L` carries opposite `edgeSign` (the conclusion of
`threshold_consecutive_opposite`, here taken as the hypothesis `hopp`), then the
sign list `L.map (edgeSign y)` is `Alternates`. This is the bridge feeding input
**C** (`halt`) of `winding_bdd_of_alternation_and_pos` without the circular detour
through `winding_bdd`. -/
lemma alternates_of_threshold_consecutive_opposite (y : ℝ) (L : List (ZMod P.n))
    (hopp : L.IsChain (fun i j => P.edgeSign y j = - P.edgeSign y i)) :
    AlternationCore.Alternates (L.map (P.edgeSign y)) := by
  apply alternates_of_chain_neg
  rw [List.isChain_map]
  exact hopp

/-- **The geometric no-nesting crux, isolated as a predicate.** Two
threshold-consecutive spanning edges carry opposite `edgeSign`: if `a, b` both
span the generic height `y`, with `edgeThr y a < edgeThr y b` and *no* spanning
edge `c` whose threshold lies strictly between (`edgeThr y a < edgeThr y c <
edgeThr y b`), then `edgeSign y b = - edgeSign y a`. This is the single remaining
topological (polygonal Jordan / planarity) input; everything downstream is
combinatorial. -/
def ThresholdConsecutiveOpposite (y : ℝ) : Prop :=
  ∀ a b : ZMod P.n, a ∈ P.spanningSet y → b ∈ P.spanningSet y →
    P.edgeThr y a < P.edgeThr y b →
    (∀ c ∈ P.spanningSet y, ¬(P.edgeThr y a < P.edgeThr y c ∧ P.edgeThr y c < P.edgeThr y b)) →
    P.edgeSign y b = - P.edgeSign y a

/-- **Winding jump across an isolated threshold.** At a generic height `y`, if the
only spanning threshold in the open interval `(xL, xR)` is that of the spanning
edge `a` (`xL < edgeThr y a < xR`, every other spanning threshold `≤ xL` or
`> xR`), then the winding drops by exactly `edgeSign y a` as `x` moves rightward
from `xL` to `xR`: `winding (xL, y) − winding (xR, y) = edgeSign y a`. This is the
algebraic seed of the ray-count argument behind `ThresholdConsecutiveOpposite`. -/
lemma winding_jump_single_threshold (y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (xL xR : ℝ) (a : ZMod P.n) (haS : a ∈ P.spanningSet y)
    (hL : xL < P.edgeThr y a) (hR : P.edgeThr y a < xR)
    (hgap : ∀ i ∈ P.spanningSet y, i ≠ a → (P.edgeThr y i ≤ xL ∨ xR < P.edgeThr y i)) :
    P.winding (xL, y) - P.winding (xR, y) = P.edgeSign y a := by
  classical
  rw [winding_eq_sum_spanning P xL y hy, winding_eq_sum_spanning P xR y hy]
  have hLR : xL < xR := lt_trans hL hR
  have hset : (P.spanningSet y).filter (fun i => xL < P.edgeThr y i)
      = insert a ((P.spanningSet y).filter (fun i => xR < P.edgeThr y i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hiS, hxL⟩
      by_cases hia : i = a
      · exact Or.inl hia
      · rcases hgap i hiS hia with h | h
        · exact absurd hxL (not_lt.mpr h)
        · exact Or.inr ⟨hiS, h⟩
    · rintro (rfl | ⟨hiS, hxR⟩)
      · exact ⟨haS, hL⟩
      · exact ⟨hiS, lt_trans hLR hxR⟩
  rw [hset, Finset.sum_insert
      (by simp only [Finset.mem_filter, not_and]; intro _; exact not_lt.mpr (le_of_lt hR))]
  ring

/-- **Isolating the two thresholds of a consecutive pair.** For a simple polygon
at a generic height, given two THRESHOLD-consecutive spanning edges `a, b`
(`edgeThr y a < edgeThr y b`, no spanning threshold strictly between), there are
three reals `xL < edgeThr y a < xm < edgeThr y b < xR` such that the open interval
`(xL, xm)` contains *only* `a`'s threshold and `(xm, xR)` contains *only* `b`'s
threshold (every other spanning threshold avoids each). This is exactly the data
two applications of `winding_jump_single_threshold` consume: distinctness of
thresholds (`crossThreshold_ne_distinct_spanning`) makes `a` the unique edge at
`edgeThr y a` and `b` the unique one at `edgeThr y b`. -/
lemma exists_isolating_points_of_consec (hP : P.IsSimple) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (a b : ZMod P.n)
    (haS : a ∈ P.spanningSet y) (hbS : b ∈ P.spanningSet y)
    (hab : P.edgeThr y a < P.edgeThr y b)
    (hbetween : ∀ c ∈ P.spanningSet y,
      ¬(P.edgeThr y a < P.edgeThr y c ∧ P.edgeThr y c < P.edgeThr y b)) :
    ∃ xL xm xR, (xL < P.edgeThr y a) ∧ (P.edgeThr y a < xm ∧ xm < P.edgeThr y b) ∧
      (P.edgeThr y b < xR) ∧
      (∀ i ∈ P.spanningSet y, i ≠ a → P.edgeThr y i ≤ xL ∨ xm < P.edgeThr y i) ∧
      (∀ i ∈ P.spanningSet y, i ≠ b → P.edgeThr y i ≤ xm ∨ xR < P.edgeThr y i) := by
  classical
  have hdist : ∀ i ∈ P.spanningSet y, ∀ j ∈ P.spanningSet y, i ≠ j →
      P.edgeThr y i ≠ P.edgeThr y j := by
    intro i hi j hj hij
    simp only [spanningSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact crossThreshold_ne_distinct_spanning P hP y hy i j hij hi hj
  obtain ⟨xL, hxLlt, hxLmax⟩ : ∃ xL, xL < P.edgeThr y a ∧
      ∀ i ∈ P.spanningSet y, P.edgeThr y i < P.edgeThr y a → P.edgeThr y i ≤ xL := by
    set S := (P.spanningSet y).filter (fun i => P.edgeThr y i < P.edgeThr y a) with hSdef
    by_cases hS : S.Nonempty
    · obtain ⟨m, hmS, hmax⟩ := S.exists_max_image (P.edgeThr y) hS
      rw [hSdef, Finset.mem_filter] at hmS
      refine ⟨(P.edgeThr y m + P.edgeThr y a) / 2, by linarith [hmS.2], ?_⟩
      intro i hiS hlt
      have := hmax i (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hiS, hlt⟩); linarith [hmS.2]
    · exact ⟨P.edgeThr y a - 1, by linarith, fun i hiS hlt =>
        absurd (Finset.mem_filter.mpr ⟨hiS, hlt⟩) (by rw [← hSdef]; exact fun hh => hS ⟨i, hh⟩)⟩
  obtain ⟨xR, hxRlt, hxRmin⟩ : ∃ xR, P.edgeThr y b < xR ∧
      ∀ i ∈ P.spanningSet y, P.edgeThr y b < P.edgeThr y i → xR < P.edgeThr y i := by
    set S := (P.spanningSet y).filter (fun i => P.edgeThr y b < P.edgeThr y i) with hSdef
    by_cases hS : S.Nonempty
    · obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (P.edgeThr y) hS
      rw [hSdef, Finset.mem_filter] at hmS
      refine ⟨(P.edgeThr y b + P.edgeThr y m) / 2, by linarith [hmS.2], ?_⟩
      intro i hiS hlt
      have := hmin i (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hiS, hlt⟩); linarith [hmS.2]
    · exact ⟨P.edgeThr y b + 1, by linarith, fun i hiS hlt =>
        absurd (Finset.mem_filter.mpr ⟨hiS, hlt⟩) (by rw [← hSdef]; exact fun hh => hS ⟨i, hh⟩)⟩
  refine ⟨xL, (P.edgeThr y a + P.edgeThr y b) / 2, xR, hxLlt,
    ⟨by linarith, by linarith⟩, hxRlt, ?_, ?_⟩
  · intro i hiS hia
    rcases lt_trichotomy (P.edgeThr y i) (P.edgeThr y a) with h | h | h
    · exact Or.inl (hxLmax i hiS h)
    · exact absurd (hdist i hiS a haS hia h) (by simp)
    · right
      have : P.edgeThr y b ≤ P.edgeThr y i := by
        by_contra hc; exact hbetween i hiS ⟨h, not_le.mp hc⟩
      linarith
  · intro i hiS hib
    rcases lt_trichotomy (P.edgeThr y b) (P.edgeThr y i) with h | h | h
    · exact Or.inr (hxRmin i hiS h)
    · exact absurd (hdist i hiS b hbS hib h.symm) (by simp)
    · left
      have : P.edgeThr y i ≤ P.edgeThr y a := by
        by_contra hc; exact hbetween i hiS ⟨not_le.mp hc, h⟩
      linarith

/-- **Two-jump form: the consecutive pair drops the winding by the sum of their
signs.** Combining `exists_isolating_points_of_consec` with
`winding_jump_single_threshold` at each of the two isolated thresholds: there are
`xL < xR` with `winding (xL, y) − winding (xR, y) = edgeSign y a + edgeSign y b`.
If the two signs were *equal* this difference would be `±2`, which the bounded
winding cannot realize — the contradiction route for `ThresholdConsecutiveOpposite`. -/
lemma winding_jump_consec (hP : P.IsSimple) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (a b : ZMod P.n)
    (haS : a ∈ P.spanningSet y) (hbS : b ∈ P.spanningSet y)
    (hab : P.edgeThr y a < P.edgeThr y b)
    (hbetween : ∀ c ∈ P.spanningSet y,
      ¬(P.edgeThr y a < P.edgeThr y c ∧ P.edgeThr y c < P.edgeThr y b)) :
    ∃ xL xR, xL < xR ∧
      P.winding (xL, y) - P.winding (xR, y) = P.edgeSign y a + P.edgeSign y b := by
  obtain ⟨xL, xm, xR, hLa, ⟨ham, hmb⟩, hbR, hgapa, hgapb⟩ :=
    exists_isolating_points_of_consec P hP y hy a b haS hbS hab hbetween
  have hja : P.winding (xL, y) - P.winding (xm, y) = P.edgeSign y a :=
    winding_jump_single_threshold P y hy xL xm a haS hLa ham hgapa
  have hjb : P.winding (xm, y) - P.winding (xR, y) = P.edgeSign y b :=
    winding_jump_single_threshold P y hy xm xR b hbS hmb hbR hgapb
  exact ⟨xL, xR, by linarith [hLa, ham, hmb, hbR], by linarith [hja, hjb]⟩

/-- **The no-nesting crux follows from a winding bound — non-circularly.** If the
winding is bounded in `{0, 1}` at every off-vertex height (`winding_bdd`), then
two threshold-consecutive spanning edges carry opposite signs. The reason: by
`winding_jump_consec` their combined drop equals `edgeSign a + edgeSign b ∈
{-2, 0, 2}`; but the drop is a difference of two bounded windings, hence lies in
`[-1, 1]`, forcing the sum to be `0`, i.e. opposite signs. This is the
`IsConnected {inside} → winding ∈ {0,1}` route's entry point into the existing
`pick_of_consec` pipeline: it supplies `ThresholdConsecutiveOpposite` from the
winding bound, *without* the combinatorial alternation argument (which itself was
used to *prove* the bound). -/
lemma thresholdConsecutiveOpposite_of_winding_bdd (hP : P.IsSimple)
    (winding_bdd : ∀ x y : ℝ, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1)
    (y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    ThresholdConsecutiveOpposite P y := by
  intro a b haS hbS hab hbetween
  obtain ⟨xL, xR, _, hjump⟩ :=
    winding_jump_consec P hP y hy a b haS hbS hab hbetween
  -- The combined drop equals signA + signB and lies in [-1, 1] (bounded windings).
  obtain ⟨hL0, hL1⟩ := winding_bdd xL y hy
  obtain ⟨hR0, hR1⟩ := winding_bdd xR y hy
  -- signA, signB ∈ {1, -1}; their sum is signA + signB and equals the drop ∈ [-1,1].
  have hsum_bnd : -1 ≤ P.edgeSign y a + P.edgeSign y b ∧
      P.edgeSign y a + P.edgeSign y b ≤ 1 := by
    rw [← hjump]; omega
  rcases edgeSign_eq_one_or_neg_one P y a with ha | ha <;>
    rcases edgeSign_eq_one_or_neg_one P y b with hb | hb <;>
    rw [ha, hb] at hsum_bnd ⊢ <;> omega

/-- A strict lower bound below every `edgeThr` of an element of a list: the
list-fold of `min (edgeThr · − 1)`. -/
lemma foldr_min_lt_edgeThr (y : ℝ) (z : ℝ) :
    ∀ (L : List (ZMod P.n)),
      ∀ c ∈ L,
        L.foldr (fun i m => min m (P.edgeThr y i - 1)) z < P.edgeThr y c := by
  intro L
  induction L with
  | nil => intro c hc; simp at hc
  | cons d t IH =>
    intro c hc
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hc with h | h
    · subst h
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · exact lt_of_le_of_lt (min_le_left _ _) (IH c h)

/-- **From the no-nesting crux to the `IsChain` of opposite signs on a
threshold-sorted list (bounded form).** Auxiliary, carrying a strict lower bound
`lo` on the thresholds of the (suffix) list, so the induction can locate any
strictly-between spanning edge inside the current tail. -/
lemma isChain_edgeSign_of_consec_aux (y : ℝ)
    (consec : ThresholdConsecutiveOpposite P y) :
    ∀ (lo : ℝ) (L : List (ZMod P.n)),
      L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j) →
      (∀ c, c ∈ L → c ∈ P.spanningSet y) →
      (∀ c ∈ P.spanningSet y, lo < P.edgeThr y c → c ∈ L) →
      (∀ c, c ∈ L → lo < P.edgeThr y c) →
      L.IsChain (fun i j => P.edgeSign y j = - P.edgeSign y i) := by
  intro lo L
  induction L generalizing lo with
  | nil => intro _ _ _ _; exact List.IsChain.nil
  | cons a t IH =>
    intro hpw hsub hsup hlo
    cases t with
    | nil => exact List.IsChain.singleton a
    | cons b s =>
      rw [List.pairwise_cons] at hpw
      obtain ⟨hab_all, hpwt⟩ := hpw
      have hab : P.edgeThr y a < P.edgeThr y b := hab_all b (by simp)
      have haS : a ∈ P.spanningSet y := hsub a (by simp)
      have hbS : b ∈ P.spanningSet y := hsub b (by simp)
      have hsub' : ∀ c, c ∈ (b :: s) → c ∈ P.spanningSet y := fun c hc => hsub c (by simp [hc])
      have hsup' : ∀ c ∈ P.spanningSet y, P.edgeThr y a < P.edgeThr y c → c ∈ (b :: s) := by
        intro c hc hac
        have hcL : c ∈ (a :: b :: s) := hsup c hc (lt_trans (hlo a (by simp)) hac)
        rcases List.mem_cons.mp hcL with h | h
        · exact absurd hac (by rw [h]; exact lt_irrefl _)
        · exact h
      have hlo' : ∀ c, c ∈ (b :: s) → P.edgeThr y a < P.edgeThr y c := by
        intro c hc; rcases List.mem_cons.mp hc with h | h
        · rw [h]; exact hab
        · exact lt_trans hab ((List.pairwise_cons.mp hpwt).1 c h)
      refine List.IsChain.cons_cons ?_ (IH (P.edgeThr y a) hpwt hsub' hsup' hlo')
      apply consec a b haS hbS hab
      intro c hcS hbetween
      obtain ⟨hac, hcb⟩ := hbetween
      have hcbs : c ∈ (b :: s) := hsup' c hcS hac
      rcases List.mem_cons.mp hcbs with h | h
      · rw [h] at hcb; exact lt_irrefl _ hcb
      · exact absurd ((List.pairwise_cons.mp hpwt).1 c h) (not_lt.mpr (le_of_lt hcb))

/-- **From the no-nesting crux to the x-sorted sign alternation.** Given the
geometric crux `ThresholdConsecutiveOpposite` and a threshold-sorted enumeration
`L` of the spanning edges, the sign list `L.map (edgeSign y)` is `Alternates` —
exactly input **C** (`halt`) of `winding_bdd_of_alternation_and_pos`, obtained
without the circular detour through `winding_bdd`. -/
lemma alternates_of_consec (y : ℝ) (consec : ThresholdConsecutiveOpposite P y)
    (L : List (ZMod P.n)) (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j)) :
    AlternationCore.Alternates (L.map (P.edgeSign y)) := by
  apply alternates_of_threshold_consecutive_opposite
  -- Use a lower bound strictly below every threshold of an element of `L`.
  set lo : ℝ := L.foldr (fun i m => min m (P.edgeThr y i - 1)) 0 with hlo_def
  refine isChain_edgeSign_of_consec_aux P y consec lo L hsorted
    (fun c hc => (hmem c).mp hc) ?_ (fun c hc => foldr_min_lt_edgeThr P y 0 L c hc)
  intro c hc _
  exact (hmem c).mpr hc

/-- **`halt` from the no-nesting crux.** For a simple polygon, given the geometric
crux `ThresholdConsecutiveOpposite` at every generic height, the x-sorted
alternating spanning list (`halt`, input **C** of
`winding_bdd_of_alternation_and_pos`) is produced at every generic height — with
**no** appeal to the winding bound (so this breaks the circularity in
`halt_of_winding_bdd`). The `Nodup`/sorted enumeration is
`spanning_threshold_nodup_sorted`; the alternation is `alternates_of_consec`. -/
lemma halt_of_consec (hP : P.IsSimple)
    (consec : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → ThresholdConsecutiveOpposite P y) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      ∃ L : List (ZMod P.n), L.Nodup ∧ (∀ i, i ∈ L ↔ i ∈ P.spanningSet y) ∧
        L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j) ∧
        AlternationCore.Alternates (L.map (P.edgeSign y)) := by
  intro y hy
  obtain ⟨L, hnodup, hmem, hsorted⟩ := spanning_threshold_nodup_sorted P hP y hy
  exact ⟨L, hnodup, hmem, hsorted, alternates_of_consec P y (consec y hy) L hmem hsorted⟩

/-- **`winding_bdd` from the no-nesting crux and positivity.** Assembles the full
generic winding bound `0 ≤ winding (x,y) ≤ 1` from the geometric crux
`ThresholdConsecutiveOpposite` (which yields the alternation `halt` directly via
`halt_of_consec`) together with the positivity input `hposline`. This is the
non-circular route into `winding_bdd_of_alternation_and_pos`. -/
lemma winding_bdd_of_consec (hP : P.IsSimple)
    (consec : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → ThresholdConsecutiveOpposite P y)
    (hposline : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y)) :
    ∀ x y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1 :=
  winding_bdd_of_alternation_and_pos P (halt_of_consec P hP consec) hposline

/-- **`winding ∈ {0,1}` a.e. from the no-nesting crux and positivity.** The
general-`n` polygonal Jordan dichotomy almost everywhere, reduced to exactly two
inputs: the geometric crux `ThresholdConsecutiveOpposite` (no-nesting) and the
positivity input `hposline`. Composes `winding_bdd_of_consec` with
`winding_ae_mem_zero_one_of_winding_bdd`. -/
lemma h01_ae_of_consec (hP : P.IsSimple)
    (consec : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → ThresholdConsecutiveOpposite P y)
    (hposline : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y)) :
    ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = 1 :=
  winding_ae_mem_zero_one_of_winding_bdd P (winding_bdd_of_consec P hP consec hposline)

/-- **Pick's theorem from the no-nesting crux, positivity, and the count.** The
full geometric area formula `area = I + B/2 − 1` for a simple polygon follows once
the three remaining inputs are supplied: the geometric no-nesting crux
`ThresholdConsecutiveOpposite` (the polygonal Jordan / planarity heart), the
positivity input `hposline` (from positive orientation), and the lattice-point
count `hcount` (Hopf angle-sum). Green's theorem is already discharged. This is
the tightest statement of what the winding route reduces `pick` to: the Jordan
crux is isolated to a single named hypothesis. -/
theorem pick_of_consec (hP : P.IsSimple)
    (consec : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → ThresholdConsecutiveOpposite P y)
    (hposline : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y))
    (hcount : ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_two_ae P (h01_ae_of_consec P hP consec hposline) hcount

/-- **Pick from a winding bound — the connectivity route's terminus.** If the
winding is bounded in `{0, 1}` at every generic height (`winding_bdd`), then Pick's
area formula holds. This routes the (independently established) bound through the
no-nesting bridge `thresholdConsecutiveOpposite_of_winding_bdd` into the
`pick_of_consec` pipeline, **non-circularly**: the bound is *not* derived from
`consec` here — it is the hypothesis. The `IsConnected {inside}` / `routing`
program targets exactly this `winding_bdd` (via value-pinning the connected
inside-winding to `1`). Together with `hposline` (positive orientation) and
`hcount` (Hopf angle-sum, discharged), it gives the full area formula. -/
theorem pick_of_winding_bdd (hP : P.IsSimple)
    (winding_bdd : ∀ x y : ℝ, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1)
    (hposline : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y))
    (hcount : ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_consec P hP
    (fun y hy => thresholdConsecutiveOpposite_of_winding_bdd P hP winding_bdd y hy)
    hposline hcount

end ParitySpanning

end Pick
