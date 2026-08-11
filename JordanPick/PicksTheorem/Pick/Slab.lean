import JordanPick.PicksTheorem.Pick.BoundaryArcs

/-!
# Pick's theorem: inside-connectivity routing (Module 5a: slab/gap routing)

The monolithic `InsideConnected` section (slab/gap routing,
`lift_across_level`, apex-cross, inside connectivity). Lives inside
`namespace Pick`. Kept as a single module because the section has no internal
clean break point.
-/

namespace Pick

open LatticePolygon

variable (P : LatticePolygon)


/-! ### The inside set is connected (Jordan core)

The entire polygonal Jordan / Pick reduction rests on the single statement that
the off-boundary `winding ≠ 0` set is connected.  We assemble it from two halves:
**nonempty** (positive orientation forces winding `≠ 0` somewhere off the
boundary, via Green's theorem) and **preconnected** (the geometric staircase
routing).  -/

section InsideConnected

open LatticePolygon MeasureTheory

variable (P : LatticePolygon)

/-- At a generic height `y` (no vertex on the line), the horizontal line meets the
boundary in a finite set of `x`-values — exactly the spanning-edge thresholds. -/
lemma lineBoundary_finite (y : ℝ) (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    Set.Finite {x : ℝ | (x, y) ∈ P.boundary} := by
  apply Set.Finite.subset
    (Set.Finite.image (fun i => P.edgeThr y i) (P.spanningSet y).finite_toSet)
  intro x hx
  obtain ⟨i, hi, hxeq⟩ := exists_spanning_threshold_of_mem_boundary P y hgen x hx
  exact ⟨i, hi, hxeq.symm⟩

/-- **A spanning edge's crossing threshold is affine in height**, hence its value at
an intermediate height `y ∈ [y₁, y₂]` lies in the (unordered) closed interval
spanned by its endpoint values. `crossThreshold a b y = a.1 + (b.1-a.1)/(b.2-a.2)·(y-a.2)`
is an affine function of `y`; this is the monotone chord-movement that makes a
horizontal gap between two spanning thresholds persist as a trapezoidal clear region
across a slab (`gap_persists_in_slab`). The slope sign is fixed by the edge, so the
threshold sweeps monotonically and stays between its slab-endpoint crossings. -/
lemma crossThreshold_mem_uIcc (a b : ℝ × ℝ) (y₁ y₂ y : ℝ) (hd : b.2 ≠ a.2)
    (h1 : y₁ ≤ y) (h2 : y ≤ y₂) :
    crossThreshold a b y ∈ Set.uIcc (crossThreshold a b y₁) (crossThreshold a b y₂) := by
  have hdd : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr hd
  set s : ℝ := (b.1 - a.1) / (b.2 - a.2) with hs
  have hrw : ∀ u : ℝ, crossThreshold a b u = a.1 + s * (u - a.2) := by
    intro u; unfold crossThreshold; rw [hs]; field_simp
  rw [hrw y, hrw y₁, hrw y₂]
  rcases le_total 0 s with hsp | hsn
  · rw [Set.uIcc_of_le (by nlinarith)]; rw [Set.mem_Icc]; constructor <;> nlinarith
  · rw [Set.uIcc_of_ge (by nlinarith)]; rw [Set.mem_Icc]; constructor <;> nlinarith

/-- The `y`-coordinate where the (non-vertical) edge `a → b` crosses abscissa `x`. -/
noncomputable def vertThr (a b : ℝ × ℝ) (x : ℝ) : ℝ :=
  a.2 + (b.2 - a.2) * (x - a.1) / (b.1 - a.1)

/-- **A point of a generic vertical line on an edge segment is its vertical
crossing threshold.** Mirror of `eq_threshold_of_mem_segment_horizontal` with the
roles of the two coordinates swapped: if `(x, y)` lies on `[a, b]` and neither
endpoint sits at abscissa `x`, then `y = vertThr a b x` (a single value). -/
lemma eq_vertThr_of_mem_segment_vertical
    (a b : ℝ × ℝ) (x y : ℝ) (hx : x ≠ a.1) (hx' : x ≠ b.1)
    (hmem : (x, y) ∈ segment ℝ a b) :
    y = vertThr a b x := by
  rw [segment_eq_image] at hmem
  obtain ⟨t, ht, hxy⟩ := hmem
  rw [Prod.ext_iff] at hxy
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
  obtain ⟨hx1, hyt⟩ := hxy
  obtain ⟨ht0, ht1⟩ := ht
  -- hx1 : (1 - t) * a.1 + t * b.1 = x ; hyt : (1 - t) * a.2 + t * b.2 = y
  have hspan : (a.1 < x ∧ x < b.1) ∨ (b.1 < x ∧ x < a.1) := by
    rcases lt_trichotomy a.1 b.1 with hab | hab | hab
    · left
      constructor
      · rcases eq_or_lt_of_le ht0 with ht0' | ht0'
        · exfalso; apply hx; rw [← hx1, ← ht0']; ring
        · nlinarith [ht0', ht1, hab]
      · rcases eq_or_lt_of_le ht1 with ht1' | ht1'
        · exfalso; apply hx'; rw [← hx1, ht1']; ring
        · nlinarith [ht0, ht1', hab]
    · exfalso; apply hx; rw [← hx1, hab]; ring
    · right
      constructor
      · rcases eq_or_lt_of_le ht1 with ht1' | ht1'
        · exfalso; apply hx'; rw [← hx1, ht1']; ring
        · nlinarith [ht0, ht1', hab]
      · rcases eq_or_lt_of_le ht0 with ht0' | ht0'
        · exfalso; apply hx; rw [← hx1, ← ht0']; ring
        · nlinarith [ht0', ht1, hab]
  have hd : b.1 - a.1 ≠ 0 := by
    rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      · intro h; have := sub_eq_zero.mp h; linarith
  have ht_eq : t = (x - a.1) / (b.1 - a.1) := by
    field_simp
    nlinarith [hx1]
  rw [← hyt, ht_eq, vertThr]
  field_simp
  ring

/-- **At a generic abscissa `x` (no vertex on the vertical line), the boundary
meets `{·.1 = x}` in finitely many `y`-values** — each edge contributes at most one
crossing `vertThr`. Vertical mirror of `lineBoundary_finite`; powers the
"clear vertical column" move of the routing argument. -/
lemma vertLineBoundary_finite (x : ℝ) (hgen : ∀ i, (toReal (P.vert i)).1 ≠ x) :
    Set.Finite {y : ℝ | (x, y) ∈ P.boundary} := by
  apply Set.Finite.subset
    (Set.Finite.image
      (fun i => vertThr (toReal (P.vert i)) (toReal (P.vert (i + 1))) x)
      (Set.finite_univ (α := ZMod P.n)))
  intro y hy
  simp only [LatticePolygon.boundary, LatticePolygon.edgeSeg, Set.mem_iUnion,
    Set.mem_ofPred_eq] at hy
  obtain ⟨i, hi⟩ := hy
  exact ⟨i, Set.mem_univ _,
    (eq_vertThr_of_mem_segment_vertical _ _ x y (hgen i).symm (hgen (i + 1)).symm hi).symm⟩

/-- **The inside set is nonempty.** For a positively-oriented polygon, Green's
theorem makes the total winding integral `= shoelace > 0`, so winding `≠ 0` on a
set of positive measure.  At a generic height the line meets the boundary in only
finitely many points, so a positive-measure (hence nonempty) set of `x` has
`winding (x, y) > 0` while `(x, y) ∉ boundary`. -/
lemma inside_nonempty (horient : P.PositivelyOriented) :
    {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0}.Nonempty := by
  classical
  obtain ⟨y, hgen, hpos⟩ := crossSection_pos_somewhere_generic P horient
  -- The line-boundary set is finite (null), so a.e. `x` is off boundary.
  have hfin := lineBoundary_finite P y hgen
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- From emptiness: every off-boundary point on the line has winding `≤ 0`.
  have hle : ∀ x : ℝ, (x, y) ∉ P.boundary → P.winding (x, y) ≤ 0 := by
    intro x hxb
    by_contra hlt
    push Not at hlt
    have : (x, y) ∈ {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0} :=
      ⟨hxb, by omega⟩
    rw [hempty] at this; exact this
  -- Hence a.e. (off the finite boundary set) `winding (x, y) ≤ 0`.
  have hae : ∀ᵐ x ∂volume, (P.winding (x, y) : ℝ) ≤ 0 := by
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ (hfin.measure_zero volume)
    intro x hx
    simp only [Set.mem_ofPred_eq, not_le] at hx
    by_contra hxb
    exact absurd (hle x hxb) (by exact_mod_cast not_le.mpr hx)
  have hle0 : (∫ x, (P.winding (x, y) : ℝ)) ≤ 0 :=
    MeasureTheory.integral_nonpos_of_ae hae
  exact absurd hle0 (not_le.mpr hpos)

/-- **A segment disjoint from the boundary is `JoinedIn` the off-boundary set.**
A segment is convex, hence path-connected; if it avoids the boundary the canonical
path between its endpoints stays in `P.boundaryᶜ`. The atomic move of the staircase
routing. -/
lemma joinedIn_boundaryCompl_of_segment {a b : ℝ × ℝ}
    (hseg : segment ℝ a b ⊆ P.boundaryᶜ) : JoinedIn P.boundaryᶜ a b := by
  have hconv : IsPathConnected (segment ℝ a b) :=
    (convex_segment a b).isPathConnected ⟨a, left_mem_segment ℝ a b⟩
  exact (hconv.joinedIn a (left_mem_segment ℝ a b) b (right_mem_segment ℝ a b)).mono hseg

/-- **Two points of a clear convex region are `JoinedIn boundaryᶜ`.** Any convex
set is path-connected; if it avoids the boundary the connecting path stays in
`P.boundaryᶜ`. The general substrate behind `joinedIn_of_no_boundary_in_rect` (open
rectangle) and the trapezoidal clear regions of the slab routing (`gap_persists_in_slab`),
where the region is an intersection of half-planes `{L(y) < x < R(y), y₁ < y < y₂}`
cut out by two affinely-moving chords. -/
lemma joinedIn_of_no_boundary_of_convex (S : Set (ℝ × ℝ))
    (hconv : Convex ℝ S) (hdisj : S ∩ P.boundary = ∅)
    {p q : ℝ × ℝ} (hp : p ∈ S) (hq : q ∈ S) :
    JoinedIn P.boundaryᶜ p q := by
  have hsub : S ⊆ P.boundaryᶜ := by
    intro z hz; rw [Set.mem_compl_iff]; intro hzb
    have : z ∈ S ∩ P.boundary := ⟨hz, hzb⟩; rw [hdisj] at this; exact this
  have hpc : IsPathConnected S := hconv.isPathConnected ⟨p, hp⟩
  exact (hpc.joinedIn p hp q hq).mono hsub

/-- The **slab gap** (trapezoid) bounded by two affinely-moving chords `aL→bL`
(left) and `aR→bR` (right) across heights `(y₁, y₂)`: the open region between the
two moving crossing thresholds. Because each `crossThreshold a b ·` is affine in
height, this is an intersection of four half-planes, hence convex. It is the
"horizontal gap swept across a slab" region of the routing argument. -/
def slabGap (aL bL aR bR : ℝ × ℝ) (y₁ y₂ : ℝ) : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ | y₁ < z.2 ∧ z.2 < y₂ ∧
    crossThreshold aL bL z.2 < z.1 ∧ z.1 < crossThreshold aR bR z.2}

/-- **The slab gap is convex.** Each bounding chord's threshold is affine in height,
so the four defining inequalities are affine in `(x, y)`; the region is an
intersection of half-planes. Convexity is exactly what makes the trapezoid
path-connected (`joinedIn_of_no_boundary_of_convex`) for the slab routing move. -/
lemma convex_slabGap (aL bL aR bR : ℝ × ℝ) (y₁ y₂ : ℝ)
    (hdL : bL.2 ≠ aL.2) (hdR : bR.2 ≠ aR.2) :
    Convex ℝ (slabGap aL bL aR bR y₁ y₂) := by
  unfold slabGap
  set sL : ℝ := (bL.1 - aL.1) / (bL.2 - aL.2) with hsL
  set sR : ℝ := (bR.1 - aR.1) / (bR.2 - aR.2) with hsR
  have hrwL : ∀ u : ℝ, crossThreshold aL bL u = aL.1 + sL * (u - aL.2) := by
    intro u; unfold crossThreshold; rw [hsL]; field_simp
  have hrwR : ∀ u : ℝ, crossThreshold aR bR u = aR.1 + sR * (u - aR.2) := by
    intro u; unfold crossThreshold; rw [hsR]; field_simp
  clear_value sL sR
  rw [convex_iff_forall_pos]
  rintro z hz w hw t u ht hu htu
  simp only [Set.mem_ofPred_eq, hrwL, hrwR] at hz hw ⊢
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  have hue : u = 1 - t := by linarith
  subst hue
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos ht (sub_pos.mpr hz1), mul_pos hu (sub_pos.mpr hw1)]
  · nlinarith [mul_pos ht (sub_pos.mpr hz2), mul_pos hu (sub_pos.mpr hw2)]
  · nlinarith [mul_pos ht (sub_pos.mpr hz3), mul_pos hu (sub_pos.mpr hw3)]
  · nlinarith [mul_pos ht (sub_pos.mpr hz4), mul_pos hu (sub_pos.mpr hw4)]

/-- **The slab gap is clear of the boundary** provided that at every height `y` in
the open slab the height is generic (no vertex on the line) and *no spanning
threshold lies strictly between the two bounding chords*. This is the precise
planarity/non-crossing input: the gap `(L(y), R(y))` stays free of crossings across
the whole slab, so by `notMem_boundary_of_between_thresholds` every point of the
trapezoid is off the boundary. -/
lemma slabGap_inter_boundary_eq_empty (aL bL aR bR : ℝ × ℝ) (y₁ y₂ : ℝ)
    (hclear : ∀ y, y₁ < y → y < y₂ → (∀ i, (toReal (P.vert i)).2 ≠ y) ∧
      (∀ i ∈ P.spanningSet y, P.edgeThr y i ≤ crossThreshold aL bL y ∨
        crossThreshold aR bR y ≤ P.edgeThr y i)) :
    slabGap aL bL aR bR y₁ y₂ ∩ P.boundary = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨x, y⟩ ⟨⟨hy1, hy2, hxL, hxR⟩, hb⟩
  obtain ⟨hgen, hgap⟩ := hclear y hy1 hy2
  exact notMem_boundary_of_between_thresholds P y hgen x
    (crossThreshold aL bL y) (crossThreshold aR bR y) ⟨hxL, hxR⟩ hgap hb

/-- **Routing across a slab through a clear gap.** Two points of the slab gap
trapezoid — at possibly different heights — are `JoinedIn P.boundaryᶜ`. This is
**step 2** of the slab routing: a horizontal gap between two non-crossing chords
persists across the slab as a connected clear region, so the gap at the lower slab
height connects to the gap at the upper height. Combines `convex_slabGap`,
`slabGap_inter_boundary_eq_empty`, and `joinedIn_of_no_boundary_of_convex`. -/
lemma joinedIn_slabGap (aL bL aR bR : ℝ × ℝ) (y₁ y₂ : ℝ)
    (hdL : bL.2 ≠ aL.2) (hdR : bR.2 ≠ aR.2)
    (hclear : ∀ y, y₁ < y → y < y₂ → (∀ i, (toReal (P.vert i)).2 ≠ y) ∧
      (∀ i ∈ P.spanningSet y, P.edgeThr y i ≤ crossThreshold aL bL y ∨
        crossThreshold aR bR y ≤ P.edgeThr y i))
    {p q : ℝ × ℝ} (hp : p ∈ slabGap aL bL aR bR y₁ y₂)
    (hq : q ∈ slabGap aL bL aR bR y₁ y₂) :
    JoinedIn P.boundaryᶜ p q :=
  joinedIn_of_no_boundary_of_convex P _ (convex_slabGap aL bL aR bR y₁ y₂ hdL hdR)
    (slabGap_inter_boundary_eq_empty P aL bL aR bR y₁ y₂ hclear) hp hq

/-- **The spanning set is constant across a vertex-free open slab.** If no vertex
height lies strictly inside `(y₁, y₂)`, then for any two heights `y, y'` in the open
slab the set of edges spanning the horizontal line is the same. Each endpoint's
side (`vert.2 < y` vs `y < vert.2`) cannot flip without a vertex crossing the slab,
so the spanning predicate is invariant. This is the combinatorial backbone that lets
the same pair of bounding chords `(aL,bL,aR,bR)` describe the gap throughout the
slab in the `route_around_chord_end` argument. -/
lemma spanningSet_const_of_slab (y₁ y₂ : ℝ)
    (hslab : ∀ i, ¬ (y₁ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y₂))
    {y y' : ℝ} (hy : y ∈ Set.Ioo y₁ y₂) (hy' : y' ∈ Set.Ioo y₁ y₂) :
    P.spanningSet y = P.spanningSet y' := by
  have key : ∀ c : ℝ, ¬ (y₁ < c ∧ c < y₂) → ((c < y) = (c < y') ∧ (y < c) = (y' < c)) := by
    intro c hc
    rw [not_and_or, not_lt, not_lt] at hc
    obtain ⟨hy1, hy2⟩ := hy; obtain ⟨hy1', hy2'⟩ := hy'
    constructor <;> · apply propext; constructor <;> intro h <;> rcases hc with hc | hc <;> linarith
  unfold LatticePolygon.spanningSet
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [(key _ (hslab i)).1, (key _ (hslab i)).2, (key _ (hslab (i+1))).1, (key _ (hslab (i+1))).2]

/-- **Chord order is preserved across a vertex-free slab.** If two spanning edges
`i, j` satisfy `edgeThr y i < edgeThr y j` at one generic height `y` of the open
slab `(y₁, y₂)` (no vertex height inside), then the strict inequality persists at
*every* height `y' ∈ (y₁, y₂)`. The thresholds are affine in height
(`crossThreshold_mem_uIcc`'s affine core) and never equal where both edges span
(`crossThreshold_ne_distinct_spanning`, valid throughout the slab by
`spanningSet_const_of_slab`), so an order swap would force an intermediate equality
— impossible. This supplies the `hclear` gap-non-crossing hypothesis of
`slabGap`/`joinedIn_slabGap` for the gap between two consecutive spanning thresholds. -/
lemma chord_order_preserved_in_slab (hP : P.IsSimple) (y₁ y₂ : ℝ)
    (hslab : ∀ i, ¬ (y₁ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y₂))
    (i j : ZMod P.n)
    {y : ℝ} (hy : y ∈ Set.Ioo y₁ y₂)
    (hi : i ∈ P.spanningSet y) (hj : j ∈ P.spanningSet y)
    (hlt : P.edgeThr y i < P.edgeThr y j)
    {y' : ℝ} (hy' : y' ∈ Set.Ioo y₁ y₂) :
    P.edgeThr y' i < P.edgeThr y' j := by
  classical
  have hgen : ∀ z, z ∈ Set.Ioo y₁ y₂ → ∀ k, (toReal (P.vert k)).2 ≠ z := by
    intro z hz k hk; exact hslab k ⟨hk ▸ hz.1, hk ▸ hz.2⟩
  have hij : i ≠ j := by rintro rfl; exact (lt_irrefl _ hlt)
  have hconst : ∀ z, z ∈ Set.Ioo y₁ y₂ → P.spanningSet z = P.spanningSet y := by
    intro z hz; exact spanningSet_const_of_slab P y₁ y₂ hslab hz hy
  have hspan : ∀ z, z ∈ Set.Ioo y₁ y₂ → ∀ k ∈ P.spanningSet y,
      ((toReal (P.vert k)).2 < z ∧ z < (toReal (P.vert (k + 1))).2) ∨
      ((toReal (P.vert (k + 1))).2 < z ∧ z < (toReal (P.vert k)).2) := by
    intro z hz k hk
    have : k ∈ P.spanningSet z := by rw [hconst z hz]; exact hk
    exact (Finset.mem_filter.mp this).2
  -- non-equality of thresholds at every slab height
  have hne : ∀ z, z ∈ Set.Ioo y₁ y₂ → P.edgeThr z i ≠ P.edgeThr z j := by
    intro z hz
    exact crossThreshold_ne_distinct_spanning P hP z (hgen z hz) i j hij
      (hspan z hz i hi) (hspan z hz j hj)
  -- non-degeneracy of the two edges
  have hdi : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by
    rcases hspan y hy i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> · intro h; linarith
  have hdj : (toReal (P.vert (j+1))).2 ≠ (toReal (P.vert j)).2 := by
    rcases hspan y hy j hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> · intro h; linarith
  -- affine representations of the two thresholds (slope `s`, base point `(b.1, b.2)`)
  obtain ⟨si, hsi⟩ : ∃ s : ℝ, ∀ z, P.edgeThr z i
      = (toReal (P.vert i)).1 + s * (z - (toReal (P.vert i)).2) := by
    refine ⟨((toReal (P.vert (i+1))).1 - (toReal (P.vert i)).1)
      / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2), fun z => ?_⟩
    unfold LatticePolygon.edgeThr crossThreshold
    have : (toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2 ≠ 0 := sub_ne_zero.mpr hdi
    field_simp
  obtain ⟨sj, hsj⟩ : ∃ s : ℝ, ∀ z, P.edgeThr z j
      = (toReal (P.vert j)).1 + s * (z - (toReal (P.vert j)).2) := by
    refine ⟨((toReal (P.vert (j+1))).1 - (toReal (P.vert j)).1)
      / ((toReal (P.vert (j+1))).2 - (toReal (P.vert j)).2), fun z => ?_⟩
    unfold LatticePolygon.edgeThr crossThreshold
    have : (toReal (P.vert (j+1))).2 - (toReal (P.vert j)).2 ≠ 0 := sub_ne_zero.mpr hdj
    field_simp
  -- `g z := edgeThr z j - edgeThr z i` is affine: `C + D·z`.
  by_contra hcon
  push Not at hcon
  have hgaff : ∀ z, (P.edgeThr z j - P.edgeThr z i)
      = ((toReal (P.vert j)).1 - (toReal (P.vert i)).1 - sj*(toReal (P.vert j)).2
          + si*(toReal (P.vert i)).2) + (sj - si)*z := by
    intro z; rw [hsi z, hsj z]; ring
  set C := (toReal (P.vert j)).1 - (toReal (P.vert i)).1 - sj*(toReal (P.vert j)).2
      + si*(toReal (P.vert i)).2 with hC
  set D := sj - si with hD
  have hgy : 0 < C + D*y := by have := hgaff y; linarith
  have hgy' : C + D*y' < 0 := by
    have h := hgaff y'
    have hne' := hne y' hy'
    rcases lt_or_eq_of_le hcon with h1 | h1
    · linarith
    · exact absurd h1.symm hne'
  have hden : 0 < (C + D*y) - (C + D*y') := by linarith
  set t := ((C+D*y) * y' - (C+D*y') * y) / ((C+D*y) - (C+D*y')) with htdef
  have htmem : t ∈ Set.Ioo y₁ y₂ := by
    obtain ⟨hy1, hy2⟩ := hy; obtain ⟨hy'1, hy'2⟩ := hy'
    constructor
    · rw [htdef, lt_div_iff₀ hden]; nlinarith
    · rw [htdef, div_lt_iff₀ hden]; nlinarith
  have hgt0 : P.edgeThr t j - P.edgeThr t i = 0 := by
    rw [hgaff t, htdef]; field_simp; nlinarith
  exact (hne t htmem) (by linarith [hgaff t])

/-- **Routing within one slab gap.** Two interior points lying in the *same* gap
between two consecutive spanning thresholds `iL < iR` (`hcons`: no other spanning
threshold lies strictly between them at the generic height `y`) — at possibly
different heights of the open vertex-free slab `(y₁, y₂)` — are `JoinedIn
boundaryᶜ`. The gap persists across the whole slab because the chord order is
preserved (`chord_order_preserved_in_slab`), making the trapezoidal `slabGap` clear
of the boundary; `joinedIn_slabGap` then connects the two points through it. This is
step 2 of the routing argument. -/
lemma joinedIn_consecutive_gap_in_slab (hP : P.IsSimple) (y₁ y₂ : ℝ)
    (hslab : ∀ i, ¬ (y₁ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y₂))
    (iL iR : ZMod P.n) {y : ℝ} (hy : y ∈ Set.Ioo y₁ y₂)
    (hiL : iL ∈ P.spanningSet y) (hiR : iR ∈ P.spanningSet y)
    (_hLR : P.edgeThr y iL < P.edgeThr y iR)
    (hcons : ∀ k ∈ P.spanningSet y, P.edgeThr y k ≤ P.edgeThr y iL ∨ P.edgeThr y iR ≤ P.edgeThr y k)
    {p q : ℝ × ℝ}
    (hp : p.2 ∈ Set.Ioo y₁ y₂ ∧ P.edgeThr p.2 iL < p.1 ∧ p.1 < P.edgeThr p.2 iR)
    (hq : q.2 ∈ Set.Ioo y₁ y₂ ∧ P.edgeThr q.2 iL < q.1 ∧ q.1 < P.edgeThr q.2 iR) :
    JoinedIn P.boundaryᶜ p q := by
  classical
  have hgen : ∀ z, z ∈ Set.Ioo y₁ y₂ → ∀ k, (toReal (P.vert k)).2 ≠ z := by
    intro z hz k hk; exact hslab k ⟨hk ▸ hz.1, hk ▸ hz.2⟩
  have hconst : ∀ z, z ∈ Set.Ioo y₁ y₂ → P.spanningSet z = P.spanningSet y := fun z hz =>
    spanningSet_const_of_slab P y₁ y₂ hslab hz hy
  have hspan : ∀ z, z ∈ Set.Ioo y₁ y₂ → ∀ k ∈ P.spanningSet y,
      ((toReal (P.vert k)).2 < z ∧ z < (toReal (P.vert (k + 1))).2) ∨
      ((toReal (P.vert (k + 1))).2 < z ∧ z < (toReal (P.vert k)).2) := by
    intro z hz k hk
    have : k ∈ P.spanningSet z := by rw [hconst z hz]; exact hk
    exact (Finset.mem_filter.mp this).2
  have hdL : (toReal (P.vert (iL+1))).2 ≠ (toReal (P.vert iL)).2 := by
    rcases hspan y hy iL hiL with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> · intro h; linarith
  have hdR : (toReal (P.vert (iR+1))).2 ≠ (toReal (P.vert iR)).2 := by
    rcases hspan y hy iR hiR with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> · intro h; linarith
  have hdistinct : ∀ z, z ∈ Set.Ioo y₁ y₂ → ∀ a b : ZMod P.n, a ∈ P.spanningSet y →
      b ∈ P.spanningSet y → a ≠ b → P.edgeThr z a ≠ P.edgeThr z b := by
    intro z hz a b ha hb hab
    exact crossThreshold_ne_distinct_spanning P hP z (hgen z hz) a b hab
      (hspan z hz a ha) (hspan z hz b hb)
  have hclear : ∀ z, y₁ < z → z < y₂ → (∀ i, (toReal (P.vert i)).2 ≠ z) ∧
      (∀ k ∈ P.spanningSet z, P.edgeThr z k ≤
          crossThreshold (toReal (P.vert iL)) (toReal (P.vert (iL+1))) z ∨
        crossThreshold (toReal (P.vert iR)) (toReal (P.vert (iR+1))) z ≤ P.edgeThr z k) := by
    intro z hz1 hz2
    have hzmem : z ∈ Set.Ioo y₁ y₂ := ⟨hz1, hz2⟩
    refine ⟨hgen z hzmem, ?_⟩
    intro k hk
    have hkY : k ∈ P.spanningSet y := by rw [← hconst z hzmem]; exact hk
    show P.edgeThr z k ≤ P.edgeThr z iL ∨ P.edgeThr z iR ≤ P.edgeThr z k
    rcases hcons k hkY with hle | hge
    · left
      by_cases hkiL : k = iL
      · rw [hkiL]
      · have hstrict : P.edgeThr y k < P.edgeThr y iL :=
          lt_of_le_of_ne hle (hdistinct y hy k iL hkY hiL hkiL)
        exact le_of_lt (chord_order_preserved_in_slab P hP y₁ y₂ hslab k iL hy hkY hiL hstrict hzmem)
    · right
      by_cases hkiR : k = iR
      · rw [hkiR]
      · have hstrict : P.edgeThr y iR < P.edgeThr y k :=
          lt_of_le_of_ne hge (Ne.symm (hdistinct y hy k iR hkY hiR hkiR))
        exact le_of_lt (chord_order_preserved_in_slab P hP y₁ y₂ hslab iR k hy hiR hkY hstrict hzmem)
  exact joinedIn_slabGap P (toReal (P.vert iL)) (toReal (P.vert (iL+1)))
    (toReal (P.vert iR)) (toReal (P.vert (iR+1))) y₁ y₂ hdL hdR hclear
    ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩ ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩

/-- **Two points of a clear axis-aligned open rectangle are `JoinedIn boundaryᶜ`.**
An open rectangle `(x₁,x₂)×(y₁,y₂)` is convex, hence path-connected; if it is
disjoint from the boundary the connecting path stays in `P.boundaryᶜ`. A reusable
2-D thickening of `joinedIn_horizontal`/`joinedIn_vertical` used to glue interior
points to a generic routing line through a clear neighbourhood. -/
lemma joinedIn_of_no_boundary_in_rect (x₁ x₂ y₁ y₂ : ℝ)
    (hdisj : (Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂) ∩ P.boundary = ∅)
    {p q : ℝ × ℝ} (hp : p ∈ Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂)
    (hq : q ∈ Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂) :
    JoinedIn P.boundaryᶜ p q := by
  have hconv : Convex ℝ (Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂) :=
    (convex_Ioo x₁ x₂).prod (convex_Ioo y₁ y₂)
  have hsub : (Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂) ⊆ P.boundaryᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzb
    have : z ∈ (Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂) ∩ P.boundary := ⟨hz, hzb⟩
    rw [hdisj] at this; exact this
  have hpc : IsPathConnected (Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂) :=
    hconv.isPathConnected ⟨p, hp⟩
  exact (hpc.joinedIn p hp q hq).mono hsub

/-- **Every off-boundary point has a clear open rectangle around it.** Since
`P.boundaryᶜ` is open it contains a metric ball; in the sup-metric of `ℝ × ℝ` an
axis-aligned box of half-side `ε/2` fits inside that ball, giving a rectangle that
contains `p` strictly and is disjoint from the boundary. Combined with
`joinedIn_of_no_boundary_in_rect` this lets any interior point reach a nearby
generic line through a clear neighbourhood. -/
lemma exists_clear_rect_at {p : ℝ × ℝ} (hp : p ∈ P.boundaryᶜ) :
    ∃ x₁ x₂ y₁ y₂ : ℝ, p ∈ Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂ ∧
      (Set.Ioo x₁ x₂ ×ˢ Set.Ioo y₁ y₂) ∩ P.boundary = ∅ := by
  have hopen := isOpen_compl_boundary P
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen p hp
  refine ⟨p.1 - ε/2, p.1 + ε/2, p.2 - ε/2, p.2 + ε/2, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩, hzb⟩
    refine (hball ?_) hzb
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    refine ⟨?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> linarith

/-- **Generic heights are dense: every nonempty open height interval contains a
height hit by no vertex.** The finitely many vertex `y`-coordinates form a closed
nowhere-dense set, so their complement is dense and meets `(a, b)`. Supplies the
`hgen` hypothesis of `lineBoundary_finite`/`notMem_boundary_of_between_thresholds`
at a height arbitrarily close to (here: strictly inside a clear box around) an
interior point. -/
lemma exists_generic_height_mem_Ioo (a b : ℝ) (hab : a < b) :
    ∃ y, a < y ∧ y < b ∧ (∀ i, (toReal (P.vert i)).2 ≠ y) := by
  classical
  have hfin : (Set.range (fun i => (toReal (P.vert i)).2)).Finite := Set.finite_range _
  have hdense : Dense ((Set.univ : Set ℝ) \ hfin.toFinset) :=
    dense_univ.sdiff_finset hfin.toFinset
  obtain ⟨y, hy, hyab⟩ := hdense.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
  exact ⟨y, hyab.1, hyab.2, fun i hi => hy.2 ((Set.Finite.mem_toFinset hfin).mpr ⟨i, hi⟩)⟩

/-- **Generic abscissae are dense.** Vertical mirror of
`exists_generic_height_mem_Ioo`: every nonempty open abscissa interval contains an
`x` hit by no vertex, supplying the `hgen` hypothesis of `vertLineBoundary_finite`
for the "clear vertical column" routing move. -/
lemma exists_generic_abscissa_mem_Ioo (a b : ℝ) (hab : a < b) :
    ∃ x, a < x ∧ x < b ∧ (∀ i, (toReal (P.vert i)).1 ≠ x) := by
  classical
  have hfin : (Set.range (fun i => (toReal (P.vert i)).1)).Finite := Set.finite_range _
  have hdense : Dense ((Set.univ : Set ℝ) \ hfin.toFinset) :=
    dense_univ.sdiff_finset hfin.toFinset
  obtain ⟨x, hx, hxab⟩ := hdense.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
  exact ⟨x, hxab.1, hxab.2, fun i hi => hx.2 ((Set.Finite.mem_toFinset hfin).mpr ⟨i, hi⟩)⟩

/-- **Open a vertex-free slab downward below a generic height.** If `y` is generic
and the open slab `(y, w)` contains no vertex height, then there is `y₀ < y` such
that the larger slab `(y₀, w)` *still* contains no vertex height. The largest vertex
height strictly below `y` (or `y - 1` if there is none) bounds the slab below. This
makes `y` itself lie *strictly inside* a vertex-free slab, so the slab-routing
lemmas (which require points strictly interior) apply at the original height `y`. -/
lemma exists_vertexFree_slab_below (y w : ℝ)
    (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (hno : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w)) :
    ∃ y₀, y₀ < y ∧ ∀ i, ¬ (y₀ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w) := by
  classical
  set S := Finset.univ.filter (fun i => (toReal (P.vert i)).2 < y) with hS
  by_cases hSne : S.Nonempty
  · obtain ⟨m, hmS, hmax⟩ := S.exists_max_image (fun i => (toReal (P.vert i)).2) hSne
    rw [hS, Finset.mem_filter] at hmS
    refine ⟨((toReal (P.vert m)).2 + y)/2, by linarith [hmS.2], ?_⟩
    intro i ⟨h1, h2⟩
    rcases lt_trichotomy (toReal (P.vert i)).2 y with hlt | heq | hgt
    · have := hmax i (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩); linarith
    · exact hgen i heq
    · exact hno i ⟨hgt, h2⟩
  · refine ⟨y - 1, by linarith, ?_⟩
    intro i ⟨h1, h2⟩
    rcases lt_trichotomy (toReal (P.vert i)).2 y with hlt | heq | hgt
    · exact hSne ⟨i, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩⟩
    · exact hgen i heq
    · exact hno i ⟨hgt, h2⟩

/-- **Drop an interior point onto a generic horizontal line.** Every off-boundary
point `p` is `JoinedIn boundaryᶜ` to a point `(p.1, y')` on a *generic* height line
(`y'` hit by no vertex, so `lineBoundary_finite` applies there). Proof: take a clear
box around `p` (`exists_clear_rect_at`), pick a generic height in its vertical span
(`exists_generic_height_mem_Ioo`), and connect within the box
(`joinedIn_of_no_boundary_in_rect`). The first routing move: from an arbitrary
interior point to the staircase grid of generic lines. -/
lemma joinedIn_to_generic_height {p : ℝ × ℝ} (hp : p ∈ P.boundaryᶜ) :
    ∃ y', (∀ i, (toReal (P.vert i)).2 ≠ y') ∧ JoinedIn P.boundaryᶜ p (p.1, y') := by
  obtain ⟨x₁, x₂, y₁, y₂, hpmem, hdisj⟩ := exists_clear_rect_at P hp
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hpmem
  obtain ⟨y', hy'1, hy'2, hgen⟩ := exists_generic_height_mem_Ioo P y₁ y₂ (lt_trans hy1 hy2)
  exact ⟨y', hgen, joinedIn_of_no_boundary_in_rect P x₁ x₂ y₁ y₂ hdisj
    ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ ⟨⟨hx1, hx2⟩, ⟨hy'1, hy'2⟩⟩⟩

/-- **A `boundaryᶜ`-path from an inside point stays inside.** Because winding is
locally constant on `P.boundaryᶜ` (`winding_const_of_isPreconnected`), any path
whose image avoids the boundary carries the constant winding value of its source.
If the source has `winding ≠ 0`, the whole path lies in the inside set. This is the
bridge converting `boundaryᶜ`-connectivity into inside-connectivity. -/
lemma joinedIn_inside_of_joinedIn_boundaryCompl {p p₀ : ℝ × ℝ}
    (hp : P.winding p ≠ 0) (hjoin : JoinedIn P.boundaryᶜ p p₀) :
    JoinedIn {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0} p p₀ := by
  obtain ⟨γ, hγ⟩ := hjoin
  refine ⟨γ, fun t => ?_⟩
  have hmemb : (γ t : ℝ × ℝ) ∉ P.boundary := hγ t
  have hpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
  have hwc : P.winding (γ t) = P.winding p := by
    apply winding_const_of_isPreconnected P _ hpre (Set.mem_range_self t)
    · exact ⟨0, γ.source⟩
    · rintro z ⟨s, rfl⟩; exact hγ s
  exact ⟨hmemb, by rw [hwc]; exact hp⟩

/-- **Connectedness from a common reference.** If every inside point is `JoinedIn`
(inside) to a fixed inside reference `p₀`, the inside set is path-connected, hence
connected. This is the final packaging of the routing argument. -/
lemma inside_isConnected_of_joinedIn_ref {p₀ : ℝ × ℝ}
    (hp₀ : p₀ ∉ P.boundary ∧ P.winding p₀ ≠ 0)
    (hjoin : ∀ p, p ∉ P.boundary → P.winding p ≠ 0 →
      JoinedIn {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0} p p₀) :
    IsConnected {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0} := by
  have hpc : IsPathConnected {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0} :=
    ⟨p₀, hp₀, fun {p} hp => (hjoin p hp.1 hp.2).symm⟩
  exact hpc.isConnected

/-- **Horizontal move off the boundary is `JoinedIn boundaryᶜ`.** If the whole
horizontal segment at height `y` between `x₁` and `x₂` avoids the boundary, its
endpoints are joined in `P.boundaryᶜ`. -/
lemma joinedIn_horizontal (y x₁ x₂ : ℝ)
    (hoff : ∀ x, x ∈ Set.uIcc x₁ x₂ → ((x, y) : ℝ × ℝ) ∉ P.boundary) :
    JoinedIn P.boundaryᶜ (x₁, y) (x₂, y) := by
  apply joinedIn_boundaryCompl_of_segment
  intro q hq
  rw [segment_eq_image] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at *
  have hy : (1 - t) * y + t * y = y := by ring
  rw [Set.mem_compl_iff]
  have hmem : ((1 - t) * x₁ + t * x₂) ∈ Set.uIcc x₁ x₂ := by
    rw [Set.uIcc_eq_union]
    rcases le_total x₁ x₂ with h | h
    · left; constructor <;> nlinarith [ht.1, ht.2]
    · right; constructor <;> nlinarith [ht.1, ht.2]
  have hb := hoff _ hmem
  intro hbd; apply hb; convert hbd using 2; exact hy.symm

/-- **Vertical move off the boundary is `JoinedIn boundaryᶜ`.** If the whole
vertical segment at abscissa `x` between `y₁` and `y₂` avoids the boundary, its
endpoints are joined in `P.boundaryᶜ`. -/
lemma joinedIn_vertical (x y₁ y₂ : ℝ)
    (hoff : ∀ y, y ∈ Set.uIcc y₁ y₂ → ((x, y) : ℝ × ℝ) ∉ P.boundary) :
    JoinedIn P.boundaryᶜ (x, y₁) (x, y₂) := by
  apply joinedIn_boundaryCompl_of_segment
  intro q hq
  rw [segment_eq_image] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at *
  have hx : (1 - t) * x + t * x = x := by ring
  rw [Set.mem_compl_iff]
  have hmem : ((1 - t) * y₁ + t * y₂) ∈ Set.uIcc y₁ y₂ := by
    rw [Set.uIcc_eq_union]
    rcases le_total y₁ y₂ with h | h
    · left; constructor <;> nlinarith [ht.1, ht.2]
    · right; constructor <;> nlinarith [ht.1, ht.2]
  have hb := hoff _ hmem
  intro hbd; apply hb; convert hbd using 2; exact hx.symm

/-- **Same-line connectivity from endpoints + clear interior.** Two points on the
same height `y`, both off the boundary, with no boundary point strictly between
their abscissae, are `JoinedIn boundaryᶜ`. Repackages `joinedIn_horizontal` so the
boundary-avoidance need only be checked on the *open* gap plus the two endpoints —
the form the routing argument actually supplies (interior intervals are open gaps
between crossings whose closures' endpoints are themselves off boundary). -/
lemma joinedIn_horizontal_of_endpoints (y x₁ x₂ : ℝ) (h12 : x₁ ≤ x₂)
    (hb1 : ((x₁, y) : ℝ × ℝ) ∉ P.boundary) (hb2 : ((x₂, y) : ℝ × ℝ) ∉ P.boundary)
    (hmid : ∀ x, x₁ < x → x < x₂ → ((x, y) : ℝ × ℝ) ∉ P.boundary) :
    JoinedIn P.boundaryᶜ (x₁, y) (x₂, y) := by
  apply joinedIn_horizontal
  intro x hx
  rw [Set.uIcc_of_le h12, Set.mem_Icc] at hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; exact hb1
  · rcases eq_or_lt_of_le hx.2 with h2 | h2
    · rw [h2]; exact hb2
    · exact hmid x h h2

/-- **Two points in the same threshold-gap of a generic line are `JoinedIn
boundaryᶜ`.** At a generic height `y`, if every spanning threshold lies either `≤ x₁`
or `≥ x₂`, then the whole open horizontal segment `(x₁, x₂) × {y}` is off the
boundary (`notMem_boundary_of_between_thresholds`), so two points `(a, y)`, `(b, y)`
with `x₁ < a, b < x₂` are joined horizontally. The atomic "slide within one gap"
move of the routing argument, packaged off the generic line. -/
lemma joinedIn_same_gap_horizontal (y : ℝ)
    (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y) (x₁ x₂ a b : ℝ)
    (ha : x₁ < a ∧ a < x₂) (hb : x₁ < b ∧ b < x₂)
    (hgap : ∀ i ∈ P.spanningSet y, P.edgeThr y i ≤ x₁ ∨ x₂ ≤ P.edgeThr y i) :
    JoinedIn P.boundaryᶜ (a, y) (b, y) := by
  have hoff : ∀ x, x₁ < x → x < x₂ → ((x, y) : ℝ × ℝ) ∉ P.boundary := fun x hx1 hx2 =>
    notMem_boundary_of_between_thresholds P y hgen x x₁ x₂ ⟨hx1, hx2⟩ hgap
  rcases le_total a b with hab | hab
  · exact joinedIn_horizontal_of_endpoints P y a b hab
      (hoff a ha.1 ha.2) (hoff b hb.1 hb.2)
      (fun x hxa hxb => hoff x (lt_trans ha.1 hxa) (lt_trans hxb hb.2))
  · exact (joinedIn_horizontal_of_endpoints P y b a hab
      (hoff b hb.1 hb.2) (hoff a ha.1 ha.2)
      (fun x hxb hxa => hoff x (lt_trans hb.1 hxb) (lt_trans hxa ha.2))).symm

/-- **Same-column connectivity from endpoints + clear interior.** Vertical mirror
of `joinedIn_horizontal_of_endpoints`: two points on the same abscissa `x`, both
off the boundary, with no boundary point strictly between their ordinates, are
`JoinedIn boundaryᶜ`. The atomic "clear vertical column" move toward the fixed
generic reference line. -/
lemma joinedIn_vertical_of_endpoints (x y₁ y₂ : ℝ) (h12 : y₁ ≤ y₂)
    (hb1 : ((x, y₁) : ℝ × ℝ) ∉ P.boundary) (hb2 : ((x, y₂) : ℝ × ℝ) ∉ P.boundary)
    (hmid : ∀ y, y₁ < y → y < y₂ → ((x, y) : ℝ × ℝ) ∉ P.boundary) :
    JoinedIn P.boundaryᶜ (x, y₁) (x, y₂) := by
  apply joinedIn_vertical
  intro y hy
  rw [Set.uIcc_of_le h12, Set.mem_Icc] at hy
  rcases eq_or_lt_of_le hy.1 with h | h
  · rw [← h]; exact hb1
  · rcases eq_or_lt_of_le hy.2 with h2 | h2
    · rw [h2]; exact hb2
    · exact hmid y h h2

/-- **Above all vertex heights the spanning set is empty.** If `Y` is strictly
greater than every vertex height, then no edge spans the line `y = Y` (both
endpoints of every edge lie strictly below `Y`), so `P.spanningSet Y = ∅`. The
"merge at the top" target of the cross-vertex routing: above the whole polygon the
horizontal line is one single boundary-free gap. -/
lemma spanningSet_empty_above (Y : ℝ) (hY : ∀ i, (toReal (P.vert i)).2 < Y) :
    P.spanningSet Y = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (hY (i+1)) (not_lt.mpr h2.le)
  · exact absurd (hY i) (not_lt.mpr h2.le)

/-- **Same-height routing reduction (skeleton).** Given the single-chord crossing
move `route_around_chord_end` — phrased as: two off-boundary points `(a,y)`, `(c,y)`
on a common generic line `y` (`a < c`) with *exactly one* spanning threshold strictly
inside `(a,c)` are `JoinedIn boundaryᶜ` — every pair of off-boundary points on the same
generic line is `JoinedIn boundaryᶜ`. Proof: strong induction on the number of
spanning thresholds strictly between the two abscissae. Zero ⟹ same gap
(`joinedIn_same_gap_horizontal`); `n+1` ⟹ peel the left-most interior threshold via
`route_around_chord_end` and recurse on the remaining `n`. This isolates the entire
remaining geometric content to `route_around_chord_end`. -/
lemma joinedIn_same_height_of_chord_end (hP : P.IsSimple) (y : ℝ)
    (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (chord_end : ∀ a c : ℝ, a < c → ((a, y) : ℝ × ℝ) ∉ P.boundary →
      ((c, y) : ℝ × ℝ) ∉ P.boundary →
      ((P.spanningSet y).filter (fun i => a < P.edgeThr y i ∧ P.edgeThr y i < c)).card = 1 →
      JoinedIn P.boundaryᶜ (a, y) (c, y))
    (a b : ℝ) (hab : a ≤ b)
    (hba : ((a, y) : ℝ × ℝ) ∉ P.boundary) (hbb : ((b, y) : ℝ × ℝ) ∉ P.boundary) :
    JoinedIn P.boundaryᶜ (a, y) (b, y) := by
  classical
  -- no spanning threshold equals an off-boundary abscissa
  have hne_thr : ∀ x : ℝ, ((x, y) : ℝ × ℝ) ∉ P.boundary → ∀ i ∈ P.spanningSet y,
      P.edgeThr y i ≠ x := by
    intro x hx i hi heq
    apply hx
    -- (x,y) lies on edge i since x = edgeThr y i and i spans y
    simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hmem : (x, y) ∈ P.edgeSeg i := by
      rw [← heq]
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact crossThreshold_mem_segment _ _ y h1 h2
      · exact crossThreshold_mem_segment_down _ _ y h1 h2
    exact Set.mem_iUnion.mpr ⟨i, hmem⟩
  -- strong induction on the number of spanning thresholds in (a, b)
  set N := fun (u v : ℝ) =>
    ((P.spanningSet y).filter (fun i => u < P.edgeThr y i ∧ P.edgeThr y i < v)).card with hN
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b → ((a, y) : ℝ × ℝ) ∉ P.boundary →
      ((b, y) : ℝ × ℝ) ∉ P.boundary → N a b = n → JoinedIn P.boundaryᶜ (a, y) (b, y) by
    exact H (N a b) a b hab hba hbb rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab hba hbb hcard
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- no spanning threshold in (a,b): same gap
      subst hn0
      have hempty : (P.spanningSet y).filter (fun i => a < P.edgeThr y i ∧ P.edgeThr y i < b) = ∅ :=
        Finset.card_eq_zero.mp hcard
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact JoinedIn.refl (by simpa using hba)
      -- every spanning threshold is ≤ a or ≥ b; off-boundary excludes equality at a,b
      have hgap : ∀ i ∈ P.spanningSet y, P.edgeThr y i ≤ a ∨ b ≤ P.edgeThr y i := by
        intro i hi
        by_contra hc
        push Not at hc
        -- a < edgeThr (strict, since ≠ a) and edgeThr < b (strict, since ≠ b)
        have hlt1 : a < P.edgeThr y i :=
          lt_of_le_of_ne hc.1.le (Ne.symm (hne_thr a hba i hi))
        have hlt2 : P.edgeThr y i < b :=
          lt_of_le_of_ne hc.2.le (hne_thr b hbb i hi)
        have : i ∈ (P.spanningSet y).filter (fun i => a < P.edgeThr y i ∧ P.edgeThr y i < b) :=
          Finset.mem_filter.mpr ⟨hi, hlt1, hlt2⟩
        rw [hempty] at this; exact absurd this (Finset.notMem_empty _)
      refine joinedIn_horizontal_of_endpoints P y a b hab hba hbb ?_
      intro x hxa hxb
      exact notMem_boundary_of_between_thresholds P y hgen x a b ⟨hxa, hxb⟩ hgap
    · -- at least one threshold strictly inside (a,b): peel the left-most one.
      set S := (P.spanningSet y).filter (fun i => a < P.edgeThr y i ∧ P.edgeThr y i < b) with hSdef
      have hScard : S.card = n := hcard
      have hSne : S.Nonempty := by
        rw [← Finset.card_pos, hScard]; omega
      obtain ⟨i₀, hi₀S, hi₀min⟩ := S.exists_min_image (P.edgeThr y) hSne
      have hi₀mem := hi₀S
      rw [hSdef, Finset.mem_filter] at hi₀mem
      obtain ⟨hi₀span, hi₀a, hi₀b⟩ := hi₀mem
      set t₀ := P.edgeThr y i₀ with ht₀
      -- the next threshold strictly above t₀ within (a,b), or b if none
      set T := S.filter (fun i => t₀ < P.edgeThr y i) with hTdef
      -- choose a cut point c
      obtain ⟨c, hac, hcb, hc_above_t₀, hc_below_next, hc_notthr⟩ :
          ∃ c, a < c ∧ c < b ∧ t₀ < c ∧
            (∀ i ∈ S, t₀ < P.edgeThr y i → c ≤ P.edgeThr y i) ∧
            (∀ i ∈ P.spanningSet y, P.edgeThr y i ≠ c) := by
        by_cases hT : T.Nonempty
        · obtain ⟨i₁, hi₁T, hi₁min⟩ := T.exists_min_image (P.edgeThr y) hT
          rw [hTdef, Finset.mem_filter] at hi₁T
          obtain ⟨hi₁S, hi₁gt⟩ := hi₁T
          have hi₁mem := hi₁S; rw [hSdef, Finset.mem_filter] at hi₁mem
          refine ⟨(t₀ + P.edgeThr y i₁) / 2, by linarith, by linarith [hi₁mem.2.2],
            by linarith, ?_, ?_⟩
          · intro i hiS hi_gt
            have := hi₁min i (by rw [hTdef, Finset.mem_filter]; exact ⟨hiS, hi_gt⟩)
            linarith
          · intro i hispan hceq
            -- c = (t₀ + edgeThr y i₁)/2 is strictly between t₀ and edgeThr y i₁; no threshold there
            by_cases hia : a < P.edgeThr y i ∧ P.edgeThr y i < b
            · have hiS : i ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hispan, hia⟩
              rcases lt_trichotomy (P.edgeThr y i) t₀ with h | h | h
              · linarith [hceq]
              · linarith [hceq]
              · have := hi₁min i (by rw [hTdef, Finset.mem_filter]; exact ⟨hiS, h⟩)
                linarith [hceq]
            · rw [not_and_or, not_lt, not_lt] at hia
              rcases hia with h | h <;> linarith [hceq]
        · -- no threshold above t₀ inside (a,b): cut between t₀ and b
          refine ⟨(t₀ + b) / 2, by linarith, by linarith, by linarith, ?_, ?_⟩
          · intro i hiS hi_gt
            exact absurd (Finset.mem_filter.mpr ⟨hiS, hi_gt⟩) (by rw [← hTdef]; exact fun h => hT ⟨i, h⟩)
          · intro i hispan hceq
            by_cases hia : a < P.edgeThr y i ∧ P.edgeThr y i < b
            · have hiS : i ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hispan, hia⟩
              rcases lt_trichotomy (P.edgeThr y i) t₀ with h | h | h
              · linarith [hceq]
              · linarith [hceq]
              · exact absurd (Finset.mem_filter.mpr ⟨hiS, h⟩) (by rw [← hTdef]; exact fun hh => hT ⟨i, hh⟩)
            · rw [not_and_or, not_lt, not_lt] at hia
              rcases hia with h | h <;> linarith [hceq]
      have hcboff : ((c, y) : ℝ × ℝ) ∉ P.boundary := by
        intro hcb'
        obtain ⟨i, hiS, hieq⟩ := exists_spanning_threshold_of_mem_boundary P y hgen c hcb'
        exact hc_notthr i hiS hieq.symm
      -- (a,c) has exactly one spanning threshold (namely i₀)
      have hcard_ac : ((P.spanningSet y).filter
          (fun i => a < P.edgeThr y i ∧ P.edgeThr y i < c)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨i₀, ?_⟩
        ext i
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hispan, hia, hic⟩
          have hib : P.edgeThr y i < b := lt_trans hic hcb
          have hiS : i ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hispan, hia, hib⟩
          by_contra hne
          -- i ≠ i₀, both in S, with edgeThr y i < c
          have hmin := hi₀min i hiS
          -- edgeThr y i ≥ t₀; if > t₀ then ≥ c (hc_below_next); contradiction with < c
          rcases lt_or_eq_of_le hmin with hlt | heq
          · have := hc_below_next i hiS hlt; linarith
          · -- edgeThr y i = t₀ = edgeThr y i₀, distinct spanning ⟹ i = i₀
            apply hne
            by_contra hii
            have hdistinct := crossThreshold_ne_distinct_spanning P hP y hgen i i₀ hii
            simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ,
              true_and] at hispan hi₀span
            exact hdistinct hispan hi₀span heq.symm
        · rintro rfl
          exact ⟨hi₀span, hi₀a, hc_above_t₀⟩
      -- connect (a,y) to (c,y) by the single-chord move
      refine (chord_end a c hac hba hcboff hcard_ac).trans ?_
      -- (c,b) has one fewer threshold
      have hcard_cb : N c b < n := by
        rw [← hcard, hN]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i₀, ?_, ?_⟩
          · rw [Finset.mem_filter]; exact ⟨hi₀span, hi₀a, hi₀b⟩
          · simp only [Finset.mem_filter, not_and]; intro _ hc'; linarith
        · intro i hi
          rw [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, lt_trans hac hi.2.1, hi.2.2⟩
      exact ih (N c b) hcard_cb c b hcb.le hcboff hbb rfl


/-- **Winding `= 1` witness at a convex lowest corner.** At the lex-lowest vertex
`m` whose two neighbours lie strictly above it and whose corner is convex
(`0 < cornerCross P m`), there is an off-boundary point `q` with `P.winding q = 1`.
The witness sits just above `vₘ`, in the band `(yₘ, yₘ+1)`, at an abscissa `xw`
just right of the incoming down-edge `m−1`'s crossing — the unique left-most
crossing of the lowest band — so that exactly the up-edge `m` and all crossings to
its right remain to the right of `xw`. The winding there is
`(∑ spanning signs) − edgeSign (m−1) = 0 − (−1) = 1`.  This is the
non-circular value-pinning of the inside winding to `1`. -/
lemma exists_winding_eq_one_of_cornerCross (hS : P.IsSimple)
    (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2)
    (hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2)
    (hcc : 0 < cornerCross P m) :
    ∃ q : ℝ × ℝ, q ∉ P.boundary ∧ P.winding q = 1 := by
  classical
  set ym := (toReal (P.vert m)).2 with hym
  set D := ∑ j, |(toReal (P.vert (j+1))).1 - (toReal (P.vert j)).1| with hD
  -- choose a generic height in the lowest band, close enough to `ym`
  have hDpos : (0:ℝ) < D + 1 := by
    have : (0:ℝ) ≤ D := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    linarith
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
    have hynn : 0 ≤ y - ym := by linarith
    have hkey : D * (1/(2*(D+1))) < 1/2 := by
      rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc D * (y - ym) ≤ D * (1/(2*(D+1))) :=
            mul_le_mul_of_nonneg_left (le_of_lt hyb) hDnn
      _ < 1/2 := hkey
  have hgen' : ∀ i, (toReal (P.vert i)).2 ≠ y := hgen
  -- separation: `m-1` and `m` are the two left-most crossings
  have hsep := lowest_band_thresholds_separate P hS m hlex hba hbc y hlo hhi hsmall
  obtain ⟨⟨hm1lt, hm0lt⟩, hother⟩ := hsep
  -- threshold order from convexity: edgeThr (m-1) < edgeThr m
  have hord : P.edgeThr y (m-1) < P.edgeThr y m :=
    (cornerCross_pos_iff_threshold_order P m y hba hbc hlo).mp hcc
  -- `m-1` spans, with sign `-1`
  have hm1S : (m - 1) ∈ P.spanningSet y := by
    rw [spanning_at_lowest_band P m hlex y hlo hhi]
    exact Or.inr ⟨by rw [sub_add_cancel], ne_of_gt hba⟩
  have hmS : m ∈ P.spanningSet y := by
    rw [spanning_at_lowest_band P m hlex y hlo hhi]
    exact Or.inl ⟨rfl, ne_of_gt hbc⟩
  have hsign : P.edgeSign y (m - 1) = -1 := by
    unfold LatticePolygon.edgeSign; rw [sub_add_cancel, if_neg (not_lt.mpr (le_of_lt hlo))]
  -- `edgeThr (m-1)` strictly below every other spanning threshold
  have hmin : ∀ i ∈ P.spanningSet y, i ≠ m - 1 → P.edgeThr y (m - 1) < P.edgeThr y i := by
    intro i hiS hine
    by_cases him : i = m
    · rw [him]; exact hord
    · exact lt_trans hm1lt (hother i hiS hine him)
  -- choose `xw` strictly between `edgeThr (m-1)` and all other thresholds
  have hmne : m ≠ m - 1 := by
    intro h; rw [← h] at hba; exact lt_irrefl _ hba
  set Sother := (P.spanningSet y).erase (m - 1) with hSother
  have hSother_ne : Sother.Nonempty := ⟨m, Finset.mem_erase.mpr ⟨hmne, hmS⟩⟩
  obtain ⟨c, hcS, hcmin⟩ := Sother.exists_min_image (P.edgeThr y) hSother_ne
  have hcmem : c ∈ P.spanningSet y := (Finset.mem_erase.mp hcS).2
  have hcne : c ≠ m - 1 := (Finset.mem_erase.mp hcS).1
  have hclt : P.edgeThr y (m - 1) < P.edgeThr y c := hmin c hcmem hcne
  set xw := (P.edgeThr y (m - 1) + P.edgeThr y c) / 2 with hxw
  have hxwL : P.edgeThr y (m - 1) < xw := by rw [hxw]; linarith
  have hxwR : ∀ i ∈ P.spanningSet y, i ≠ m - 1 → xw < P.edgeThr y i := by
    intro i hiS hine
    have : P.edgeThr y c ≤ P.edgeThr y i :=
      hcmin i (Finset.mem_erase.mpr ⟨hine, hiS⟩)
    rw [hxw]; linarith
  -- the witness point is off the boundary
  refine ⟨(xw, y), ?_, ?_⟩
  · intro hb
    obtain ⟨i, hiS, hxeq⟩ := exists_spanning_threshold_of_mem_boundary P y hgen' xw hb
    by_cases hine : i = m - 1
    · rw [hine] at hxeq; rw [hxeq] at hxwL; exact lt_irrefl _ hxwL
    · have := hxwR i hiS hine; rw [hxeq] at this; exact lt_irrefl _ this
  · -- winding (xw,y) = total - edgeSign (m-1) = 0 - (-1) = 1
    rw [winding_eq_sum_spanning P xw y hgen']
    have hset : (P.spanningSet y).filter (fun i => xw < P.edgeThr y i)
        = (P.spanningSet y).erase (m - 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hiS, hlt⟩
        exact ⟨by rintro rfl; exact absurd hxwL (not_lt.mpr (le_of_lt hlt)), hiS⟩
      · rintro ⟨hne, hiS⟩; exact ⟨hiS, hxwR i hiS hne⟩
    rw [hset, Finset.sum_erase_eq_sub hm1S, sum_edgeSign_spanning_eq_zero P y hgen', hsign]
    ring

/-- A nondegenerate segment in the plane is Lebesgue-null: it lies in the affine
span of its two distinct endpoints, a line (a proper affine subspace of `ℝ²`). -/
lemma volume_segment_eq_zero {a b : ℝ × ℝ} (hab : a ≠ b) :
    MeasureTheory.volume (segment ℝ a b) = 0 := by
  have hsub : segment ℝ a b ⊆ (affineSpan ℝ {a, b} : Set (ℝ × ℝ)) := by
    rw [← convexHull_pair]; exact convexHull_subset_affineSpan {a, b}
  refine MeasureTheory.measure_mono_null hsub ?_
  apply MeasureTheory.Measure.addHaar_affineSubspace
  -- the affine span of two distinct points is a line, not the whole plane
  intro htop
  have hcard : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range ![a, b])) + 1
      ≤ Fintype.card (Fin 2) := finrank_vectorSpan_range_add_one_le ℝ ![a, b]
  have hrange : Set.range ![a, b] = {a, b} := by
    rw [Set.range_eq_iff]; constructor
    · intro i; fin_cases i <;> simp
    · intro x hx; rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [hrange] at hcard
  -- if affineSpan = ⊤ then vectorSpan = ⊤, so finrank = 2, contradicting ≤ 1
  have hvs : vectorSpan ℝ ({a, b} : Set (ℝ × ℝ)) = ⊤ := by
    have := AffineSubspace.direction_eq_top_iff_of_nonempty
      (s := affineSpan ℝ ({a, b} : Set (ℝ × ℝ)))
      ⟨a, subset_affineSpan ℝ _ (by left; rfl)⟩
    rw [direction_affineSpan] at this
    exact this.mpr htop
  rw [hvs] at hcard
  simp only [finrank_top, Module.finrank_prod, Module.finrank_self,
    Fintype.card_fin] at hcard
  omega

/-- The polygon boundary (a finite union of nondegenerate edge segments) is
Lebesgue-null. Hence a.e. plane point is off the boundary. -/
lemma volume_boundary_eq_zero (hS : P.IsSimple) :
    MeasureTheory.volume P.boundary = 0 := by
  classical
  unfold LatticePolygon.boundary
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro i
  unfold LatticePolygon.edgeSeg
  exact volume_segment_eq_zero (fun h => hS.1 i (toReal_injective h))

/-- **`|winding| = 1` witness (Task A), fully general — NO convexity, NO lowest
band.** For a simple, positively-oriented polygon there is an off-boundary point `q`
with `winding q = 1 ∨ winding q = -1`. Proof: positive orientation gives a generic
height `y` whose cross-section integral is positive, hence the spanning set there is
nonempty. Among the (finitely many) spanning edges pick the one `a` with the
*smallest* crossing threshold — unique by `crossThreshold_ne_distinct_spanning`
(simplicity). Place `xw` strictly between `edgeThr y a` and the second-smallest
threshold. Then `winding (xw, y) = (∑ all spanning signs) − edgeSign y a
= 0 − edgeSign y a = ± 1`, since every spanning edge except `a` has threshold
`> xw` and `a` itself has threshold `< xw`. The point is off the boundary because
`xw` avoids every spanning threshold. -/
lemma exists_abs_winding_eq_one (hS : P.IsSimple) (horient : P.PositivelyOriented) :
    ∃ q : ℝ × ℝ, q ∉ P.boundary ∧ (P.winding q = 1 ∨ P.winding q = -1) := by
  classical
  obtain ⟨y, hgen, hpos⟩ := crossSection_pos_somewhere_generic P horient
  -- spanning set is nonempty (else winding ≡ 0 on the line, integral 0)
  have hSne : (P.spanningSet y).Nonempty := by
    rcases (P.spanningSet y).eq_empty_or_nonempty with hE | hN
    · exfalso
      have hzero : ∀ x, P.winding (x, y) = 0 := by
        intro x; rw [winding_eq_sum_spanning P x y hgen, hE]; simp
      have : (∫ x, (P.winding (x, y) : ℝ)) = 0 := by
        simp only [hzero]; simp
      rw [this] at hpos; exact lt_irrefl _ hpos
    · exact hN
  -- smallest-threshold spanning edge `a`
  obtain ⟨a, haS, hamin⟩ := (P.spanningSet y).exists_min_image (P.edgeThr y) hSne
  -- thresholds of distinct spanning edges are distinct, so `a` is the strict min
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
  -- the erased set is nonempty: an odd spanning count would make the sign-sum ± odd ≠ 0
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
  -- second-smallest threshold among the others, and xw strictly between
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
  · -- off boundary: xw avoids every spanning threshold
    intro hb
    obtain ⟨i, hiS, hxeq⟩ := exists_spanning_threshold_of_mem_boundary P y hgen xw hb
    by_cases hia : i = a
    · rw [hia] at hxeq; rw [hxeq] at hxwL; exact lt_irrefl _ hxwL
    · have := hxwR i hiS hia; rw [hxeq] at this; exact lt_irrefl _ this
  · -- winding (xw,y) = (∑ all) − edgeSign a = 0 − edgeSign a = ±1
    rw [winding_eq_sum_spanning P xw y hgen]
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

/-- **Value-pinning from connectivity (Task B core).** If the inside set
`{q ∉ boundary ∧ winding q ≠ 0}` is connected, then `winding ∈ {0,1}` almost
everywhere. Proof: connectedness makes `winding` constant `= v` on the (open,
off-boundary) inside set; the Task A witness `exists_abs_winding_eq_one` (an inside
point with `winding = ±1`) pins `v ∈ {1,-1}`. Off the null boundary, every point
either has `winding = 0` or lies in the inside set (so `winding = v`), giving
`∀ᵐ q, winding q = 0 ∨ winding q = v`. Finally `∫ winding = shoelace > 0` (Green +
positive orientation) excludes `v = -1`, so `v = 1`. -/
lemma h01_ae_of_inside_isConnected (hS : P.IsSimple) (horient : P.PositivelyOriented)
    (hconn : IsConnected {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0}) :
    ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = 1 := by
  classical
  set s := {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0} with hs
  have hsub : s ⊆ P.boundaryᶜ := fun q hq => hq.1
  -- winding is constant `= v` on the connected inside set
  obtain ⟨w, hwb, hwabs⟩ := exists_abs_winding_eq_one P hS horient
  have hws : w ∈ s := ⟨hwb, by rcases hwabs with h | h <;> rw [h] <;> norm_num⟩
  set v := P.winding w with hv
  have hconst : ∀ q ∈ s, P.winding q = v := fun q hq =>
    winding_const_of_isPreconnected P hsub hconn.2 hq hws
  -- v = ±1
  have hvval : v = 1 ∨ v = -1 := by rw [hv]; exact hwabs
  -- a.e. off the null boundary, winding ∈ {0, v}
  have hbnull : P.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero P hS
  have hae0v : ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = v := by
    filter_upwards [hbnull] with q hq
    by_cases hw0 : P.winding q = 0
    · exact Or.inl hw0
    · exact Or.inr (hconst q ⟨hq, hw0⟩)
  -- exclude v = -1 via positive total integral
  have hvpos : v = 1 := by
    rcases hvval with h1 | hm1
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

/-- **`pick` from `inside_isConnected` (Task B milestone).** The full area formula
`area = I + B/2 − 1` for a simple, positively-oriented lattice polygon follows from
just two inputs: the connectivity of the inside set (the sole remaining geometric
content of the polygonal Jordan curve theorem) and the lattice-point count `hcount`
(the Hopf angle-sum, a separate combinatorial obligation). Green's theorem is
already discharged. This reduces the whole winding route to `inside_isConnected`:
connectivity ⟹ `winding ∈ {0,1}` a.e. (value-pinned to `1` by Green + positive
orientation), then `pick_of_two_ae`. -/
theorem pick_of_inside_isConnected (hS : P.IsSimple) (horient : P.PositivelyOriented)
    (hconn : IsConnected {q : ℝ × ℝ | q ∉ P.boundary ∧ P.winding q ≠ 0})
    (hcount : ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_two_ae P (h01_ae_of_inside_isConnected P hS horient hconn) hcount


end InsideConnected

end Pick
