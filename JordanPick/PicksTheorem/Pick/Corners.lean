import JordanPick.PicksTheorem.Pick.Alternation

/-!
# Pick's theorem: corners and ear-existence scaffolding (Module 3)

Ear-existence scaffolding (`inTriangle`, `cornerCross`, `isEarVertex`, fan
lemmas, lex-lowest orientation) and the angular preorder. Lives inside
`namespace Pick`.
-/

namespace Pick

open LatticePolygon

variable (P : LatticePolygon)

/-! ## Ear-existence scaffolding (Step 1 of the ear provider)

This block introduces the geometric predicates for ear-clipping: membership in a
closed triangle (`inTriangle`), the convex/empty-ear predicate (`isEarVertex`),
trivial membership API, and the lex-lowest-vertex *configuration* facts (the two
incident edge vectors point lexicographically "up"). The convex-vertex sign
(`0 < cross …` at the lowest vertex) is the deep global-orientation step still
to be supplied (see `lex_lowest_edge_signs` for the local content that is
unconditionally true). -/

/-- `p` lies in the **closed** triangle `a b c` (counterclockwise convention):
it is weakly to the left of each directed edge `a→b`, `b→c`, `c→a`. The three
cross signs mirror the interiority test of `angleWeight_interior_triangle`. -/
def inTriangle (a b c p : ℝ × ℝ) : Prop :=
  0 ≤ cross (b - a) (p - a) ∧ 0 ≤ cross (c - b) (p - b) ∧ 0 ≤ cross (a - c) (p - c)

/-- The first corner `a` of a CCW triangle lies in its own closed triangle. -/
lemma inTriangle_fst (a b c : ℝ × ℝ) (h : 0 ≤ cross (b - a) (c - a)) :
    inTriangle a b c a := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cross]
  · have e : cross (c - b) (a - b) = cross (b - a) (c - a) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; exact h
  · rw [cross_self]

/-- The second corner `b` lies in the closed CCW triangle `a b c`. -/
lemma inTriangle_snd (a b c : ℝ × ℝ) (h : 0 ≤ cross (b - a) (c - a)) :
    inTriangle a b c b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cross_self]
  · simp [cross]
  · have e : cross (a - c) (b - c) = cross (b - a) (c - a) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; exact h

/-- The third corner `c` lies in the closed CCW triangle `a b c`. -/
lemma inTriangle_thd (a b c : ℝ × ℝ) (h : 0 ≤ cross (b - a) (c - a)) :
    inTriangle a b c c := by
  refine ⟨?_, ?_, ?_⟩
  · exact h
  · rw [cross_self]
  · simp [cross]

/-- **The base edge `[a, c]` lies in the closed CCW triangle `a b c`.** Any point of
the segment between two corners of a positively-oriented (`0 ≤ cross (b−a) (c−a)`)
triangle satisfies the three `inTriangle` half-plane tests. -/
lemma inTriangle_of_mem_segment_fst_thd (a b c p : ℝ × ℝ)
    (h : 0 ≤ cross (b - a) (c - a)) (hp : p ∈ segment ℝ a c) :
    inTriangle a b c p := by
  rw [segment_eq_image] at hp
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hp
  have hh : 0 ≤ cross (b - a) (c - a) := h
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at hh
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul] <;>
    nlinarith [mul_nonneg ht0 hh, mul_nonneg (sub_nonneg.2 ht1) hh, ht0, ht1]

/-- The **convex corner cross** at vertex `i`: the turn from the incoming edge
`vᵢ₋₁→vᵢ` to the outgoing edge `vᵢ→vᵢ₊₁`. Positive = left turn (convex, CCW). -/
def cornerCross (P : LatticePolygon) (i : ZMod P.n) : ℝ :=
  cross (toReal (P.vert i) - toReal (P.vert (i - 1)))
        (toReal (P.vert (i + 1)) - toReal (P.vert i))

/-- `i` is an **ear vertex**: its corner is a strict left turn (convex) and no
other polygon vertex lies in the closed ear triangle `(vᵢ₋₁, vᵢ, vᵢ₊₁)`. The
ear can then be clipped. -/
def isEarVertex (P : LatticePolygon) (i : ZMod P.n) : Prop :=
  0 < cornerCross P i ∧
    ∀ j, j ≠ i - 1 → j ≠ i → j ≠ i + 1 →
      ¬ inTriangle (toReal (P.vert (i - 1))) (toReal (P.vert i))
        (toReal (P.vert (i + 1))) (toReal (P.vert j))

/-- **Lex-lowest configuration (local, unconditional).** At the
lexicographically-lowest vertex `m` (minimal `y`, ties by minimal `x`), the
incoming edge vector `vₘ − vₘ₋₁` points lexicographically down (`y ≤ 0`, and
`x < 0` when `y = 0`) and the outgoing edge vector `vₘ₊₁ − vₘ` points
lexicographically up. These are exactly the constraints that, together with
**global** positive orientation, force the corner cross `> 0` (the remaining
deep step). Here we record the unconditional half. -/
lemma lex_lowest_edge_signs (P : LatticePolygon) (hS : P.IsSimple) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1)) :
    (toReal (P.vert (m + 1)) - toReal (P.vert m)).2 ≥ 0 ∧
    (toReal (P.vert m) - toReal (P.vert (m - 1))).2 ≤ 0 ∧
    ((toReal (P.vert (m + 1)) - toReal (P.vert m)).2 = 0 →
      0 < (toReal (P.vert (m + 1)) - toReal (P.vert m)).1) ∧
    ((toReal (P.vert m) - toReal (P.vert (m - 1))).2 = 0 →
      (toReal (P.vert m) - toReal (P.vert (m - 1))).1 < 0) := by
  have hdeg := hS.1
  -- unpack the lex order at the two neighbors
  have hnext := hlex (m + 1)
  have hprev := hlex (m - 1)
  rw [Prod.Lex.toLex_le_toLex] at hnext hprev
  simp only [toReal, Prod.fst_sub, Prod.snd_sub, ge_iff_le, sub_nonneg, sub_nonpos]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (vert (m+1)).2 ≥ (vert m).2
    rcases hnext with h | ⟨he, _⟩
    · exact_mod_cast le_of_lt h
    · exact_mod_cast le_of_eq he
  · -- (vert m).2 ≤ (vert (m-1)).2
    rcases hprev with h | ⟨he, _⟩
    · exact_mod_cast le_of_lt h
    · exact_mod_cast le_of_eq he
  · -- if heights equal at next, x strictly increases
    intro hy
    have hy' : ((P.vert m).2 : ℝ) = ((P.vert (m + 1)).2 : ℝ) := by
      have : ((P.vert (m + 1)).2 : ℝ) - ((P.vert m).2 : ℝ) = 0 := hy
      linarith
    have hyZ : (P.vert m).2 = (P.vert (m + 1)).2 := by exact_mod_cast hy'
    rcases hnext with h | ⟨_, hx⟩
    · exact absurd hyZ (by exact_mod_cast ne_of_lt h)
    · have hxlt : (P.vert m).1 ≤ (P.vert (m + 1)).1 := hx
      rcases lt_or_eq_of_le hxlt with hlt | heq
      · have : (P.vert m).1 < (P.vert (m + 1)).1 := hlt
        have h2 : ((P.vert m).1 : ℝ) < ((P.vert (m + 1)).1 : ℝ) := by exact_mod_cast this
        linarith
      · exact absurd (Prod.ext heq hyZ : P.vert m = P.vert (m + 1)) (hdeg m)
  · -- if heights equal at prev, x strictly decreases
    intro hy
    have hy' : ((P.vert (m - 1)).2 : ℝ) = ((P.vert m).2 : ℝ) := by
      have : ((P.vert m).2 : ℝ) - ((P.vert (m - 1)).2 : ℝ) = 0 := hy
      linarith
    have hyZ : (P.vert (m - 1)).2 = (P.vert m).2 := by exact_mod_cast hy'
    rcases hprev with h | ⟨_, hx⟩
    · exact absurd hyZ.symm (by exact_mod_cast ne_of_lt h)
    · have hxlt : (P.vert m).1 ≤ (P.vert (m - 1)).1 := hx
      rcases lt_or_eq_of_le hxlt with hlt | heq
      · have : (P.vert m).1 < (P.vert (m - 1)).1 := hlt
        have h2 : ((P.vert m).1 : ℝ) < ((P.vert (m - 1)).1 : ℝ) := by exact_mod_cast this
        linarith
      · have : P.vert (m - 1) = P.vert m := Prod.ext heq.symm hyZ
        have hd : P.vert (m - 1) ≠ P.vert ((m - 1) + 1) := hdeg (m - 1)
        rw [sub_add_cancel] at hd
        exact absurd this hd

/-- **All vertices lie weakly above the lex-lowest vertex.** At the
lexicographically-lowest vertex `m` (minimal `y`, ties by minimal `x`), every
other vertex has `y`-coordinate `≥ vₘ.2`. The horizontal supporting line through
`vₘ` is a closed lower bound for the whole vertex set. -/
lemma lex_lowest_all_above (P : LatticePolygon) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1)) :
    ∀ j, (toReal (P.vert m)).2 ≤ (toReal (P.vert j)).2 := by
  intro j
  have h := hlex j
  rw [Prod.Lex.toLex_le_toLex] at h
  simp only [toReal]
  rcases h with h | ⟨he, _⟩
  · exact_mod_cast le_of_lt h
  · exact_mod_cast le_of_eq he

/-- **Lowest-band height dichotomy.** Fix the lex-lowest vertex `m` and a height
`y` strictly inside the lowest unit band `(yₘ, yₘ+1)`. Because every vertex lies
weakly above `yₘ` and all heights are integers, a vertex `j` is *below* `y` iff it
sits exactly at the minimum height `yₘ`; otherwise it is strictly above `y`. -/
lemma lowest_band_below_iff_min (P : LatticePolygon) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (y : ℝ) (hlo : (toReal (P.vert m)).2 < y) (hhi : y < (toReal (P.vert m)).2 + 1)
    (j : ZMod P.n) :
    (toReal (P.vert j)).2 < y ↔ (toReal (P.vert j)).2 = (toReal (P.vert m)).2 := by
  have hmin : (toReal (P.vert m)).2 ≤ (toReal (P.vert j)).2 := lex_lowest_all_above P m hlex j
  simp only [toReal] at *
  constructor
  · intro hjy
    by_contra hne
    have hlt : ((P.vert m).2 : ℝ) < ((P.vert j).2 : ℝ) := lt_of_le_of_ne hmin (Ne.symm hne)
    have hZ : (P.vert m).2 < (P.vert j).2 := by exact_mod_cast hlt
    have hZ1 : (P.vert m).2 + 1 ≤ (P.vert j).2 := by omega
    have hR1 : ((P.vert m).2 : ℝ) + 1 ≤ ((P.vert j).2 : ℝ) := by exact_mod_cast hZ1
    linarith
  · intro he
    rw [he]; exact hlo

/-- **A vertex strictly above the lowest band.** Same setup: any vertex not at the
minimum height has height `≥ yₘ+1 > y`, hence is strictly above `y`. -/
lemma lowest_band_above_of_ne_min (P : LatticePolygon) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (y : ℝ) (hhi : y < (toReal (P.vert m)).2 + 1)
    (j : ZMod P.n) (hne : (toReal (P.vert j)).2 ≠ (toReal (P.vert m)).2) :
    y < (toReal (P.vert j)).2 := by
  have hmin : (toReal (P.vert m)).2 ≤ (toReal (P.vert j)).2 := lex_lowest_all_above P m hlex j
  simp only [toReal] at *
  have hlt : ((P.vert m).2 : ℝ) < ((P.vert j).2 : ℝ) := lt_of_le_of_ne hmin (Ne.symm hne)
  have hZ : (P.vert m).2 < (P.vert j).2 := by exact_mod_cast hlt
  have hZ1 : (P.vert m).2 + 1 ≤ (P.vert j).2 := by omega
  have hR1 : ((P.vert m).2 : ℝ) + 1 ≤ ((P.vert j).2 : ℝ) := by exact_mod_cast hZ1
  linarith

/-- **Threshold of a lowest-band up-edge stays near its bottom vertex.** For an edge
`a → b` with `a` at the band-floor `ym` and `b` at height `≥ ym+1`, at a height `y`
in the band `(ym, ym+1)` the crossing `x`-coordinate lies within `|Δx|·(y−ym)` of
the floor vertex's abscissa `a.1`. The crossing snaps to the floor vertex as
`y ↓ ym`; the `|Δx|·(y−ym)` modulus is what makes the lowest two crossings the
left-most ones for `y` close enough to `ym`. -/
lemma crossThreshold_near_floor_src (a b : ℝ × ℝ) (ym y : ℝ)
    (hamin : a.2 = ym) (hbove : ym + 1 ≤ b.2) (hlo : ym < y) :
    |crossThreshold a b y - a.1| ≤ |b.1 - a.1| * (y - ym) := by
  unfold crossThreshold
  have hd : (0:ℝ) < b.2 - a.2 := by rw [hamin]; linarith
  rw [show a.1 + (b.1 - a.1) * (y - a.2) / (b.2 - a.2) - a.1
      = (b.1 - a.1) * (y - a.2) / (b.2 - a.2) by ring, abs_div, abs_mul, abs_of_pos hd,
    div_le_iff₀ hd, abs_of_pos (show (0:ℝ) < y - a.2 by rw [hamin]; linarith)]
  rw [show y - a.2 = y - ym by rw [hamin]]
  exact le_mul_of_one_le_right (by positivity) (by linarith)

/-- **Threshold of a lowest-band down-edge stays near its bottom vertex.** Mirror of
`crossThreshold_near_floor_src` for an edge `a → b` whose *terminal* vertex `b` is
at the band-floor (`a` above): the crossing `x` snaps to `b.1`, within
`|Δx|·(y−ym)`. -/
lemma crossThreshold_near_floor_tgt (a b : ℝ × ℝ) (ym y : ℝ)
    (hbmin : b.2 = ym) (haove : ym + 1 ≤ a.2) (hlo : ym < y) :
    |crossThreshold a b y - b.1| ≤ |b.1 - a.1| * (y - ym) := by
  unfold crossThreshold
  have hd : (0:ℝ) < a.2 - b.2 := by rw [hbmin]; linarith
  have hdne : b.2 - a.2 ≠ 0 := by rw [hbmin]; intro h; nlinarith
  rw [show a.1 + (b.1 - a.1) * (y - a.2) / (b.2 - a.2) - b.1
      = (b.1 - a.1) * (y - b.2) / (b.2 - a.2) by field_simp; ring, abs_div, abs_mul]
  rw [show |b.2 - a.2| = a.2 - b.2 from by rw [abs_of_neg (by linarith)]; ring, div_le_iff₀ hd,
    abs_of_pos (show (0:ℝ) < y - b.2 by rw [hbmin]; linarith)]
  rw [show y - b.2 = y - ym by rw [hbmin]]
  exact le_mul_of_one_le_right (by positivity) (by linarith)

/-- **STEP 1 — Spanning edges in the lowest band are exactly the edges incident to a
minimum-height vertex.** Fix the lex-lowest vertex `m` and a generic height `y`
strictly inside the lowest unit band `(yₘ, yₘ+1)` (so no vertex sits at height
`y`). An edge `i` spans `y` iff exactly one of its two endpoints sits at the
minimum height `yₘ` (the other being strictly above, at height `≥ yₘ+1`). This
reduces the winding cross-section at `y` to a finite sum over the edges incident to
the lowest vertices — the local, non-circular description of the winding just above
`vₘ`. -/
lemma spanning_at_lowest_band (P : LatticePolygon) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (y : ℝ) (hlo : (toReal (P.vert m)).2 < y) (hhi : y < (toReal (P.vert m)).2 + 1)
    (i : ZMod P.n) :
    i ∈ P.spanningSet y ↔
      ((toReal (P.vert i)).2 = (toReal (P.vert m)).2 ∧
          (toReal (P.vert (i + 1))).2 ≠ (toReal (P.vert m)).2) ∨
      ((toReal (P.vert (i + 1))).2 = (toReal (P.vert m)).2 ∧
          (toReal (P.vert i)).2 ≠ (toReal (P.vert m)).2) := by
  classical
  unfold spanningSet
  rw [Finset.mem_filter]
  have hbi := lowest_band_below_iff_min P m hlex y hlo hhi i
  have hbi1 := lowest_band_below_iff_min P m hlex y hlo hhi (i + 1)
  constructor
  · rintro ⟨_, hsp⟩
    rcases hsp with ⟨hb, ha⟩ | ⟨hb, ha⟩
    · -- vert i below (=min), vert (i+1) above (≠min)
      refine Or.inl ⟨hbi.mp hb, ?_⟩
      intro hcon
      exact absurd (hbi1.mpr hcon) (not_lt.mpr (le_of_lt ha))
    · -- vert (i+1) below (=min), vert i above (≠min)
      refine Or.inr ⟨hbi1.mp hb, ?_⟩
      intro hcon
      exact absurd (hbi.mpr hcon) (not_lt.mpr (le_of_lt ha))
  · rintro (⟨hi, hi1⟩ | ⟨hi1, hi⟩)
    · refine ⟨Finset.mem_univ _, Or.inl ⟨hbi.mpr hi, ?_⟩⟩
      exact lowest_band_above_of_ne_min P m hlex y hhi (i + 1) hi1
    · refine ⟨Finset.mem_univ _, Or.inr ⟨hbi1.mpr hi1, ?_⟩⟩
      exact lowest_band_above_of_ne_min P m hlex y hhi i hi

/-- **Corner-cross / threshold-gap identity (apex below).** Three points `a, b, c`
with the middle point `b` strictly below `a` and `c`, and a query height `y`
strictly between `b.2` and both `a.2, c.2`. Then the signed gap between the two
crossing columns of the edges `a→b` (down-edge, threshold `crossThreshold a b y`)
and `b→c` (up-edge, threshold `crossThreshold b c y`), scaled by the positive
product `(a.2−b.2)(c.2−b.2)`, equals the corner cross `cross (b−a) (c−b)` scaled by
the positive height gap `(y−b.2)`. Hence the two have the **same sign**: the corner
turns left (`cross > 0`) iff the outgoing up-crossing lies right of the incoming
down-crossing in the band just above the apex. -/
lemma crossThreshold_gap_eq_cornerCross (a b c : ℝ × ℝ) (y : ℝ)
    (hba : b.2 < a.2) (hbc : b.2 < c.2) (_hby : b.2 < y) :
    (crossThreshold b c y - crossThreshold a b y) * ((a.2 - b.2) * (c.2 - b.2))
      = cross (b - a) (c - b) * (y - b.2) := by
  unfold crossThreshold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  have h1 : a.2 - b.2 ≠ 0 := by intro h; nlinarith
  have h2 : c.2 - b.2 ≠ 0 := by intro h; nlinarith
  have hd1 : b.2 - a.2 ≠ 0 := by intro h; nlinarith
  have hd2 : c.2 - b.2 ≠ 0 := h2
  field_simp
  ring

/-- **STEP 2 — Corner sign = band threshold order.** At the lex-lowest vertex `m`
(apex `vₘ` strictly below both neighbours `vₘ₋₁, vₘ₊₁`), pick any height `y`
strictly between `yₘ` and `min(yₘ₋₁, yₘ₊₁)`. Then `cornerCross P m > 0` iff the
outgoing up-edge `m`'s crossing column is strictly right of the incoming down-edge
`(m−1)`'s crossing column at height `y`:
`cornerCross P m > 0 ↔ P.edgeThr y (m−1) < P.edgeThr y m`.
This converts the corner-convexity question at the lowest vertex into a purely
local comparison of the two ray-crossings in the band just above `vₘ`. -/
lemma cornerCross_pos_iff_threshold_order (P : LatticePolygon) (m : ZMod P.n)
    (y : ℝ)
    (hba : (toReal (P.vert (m - 1))).2 > (toReal (P.vert m)).2)
    (hbc : (toReal (P.vert (m + 1))).2 > (toReal (P.vert m)).2)
    (hby : (toReal (P.vert m)).2 < y) :
    0 < cornerCross P m ↔ P.edgeThr y (m - 1) < P.edgeThr y m := by
  set a := toReal (P.vert (m - 1)) with ha
  set b := toReal (P.vert m) with hb
  set c := toReal (P.vert (m + 1)) with hc
  -- cornerCross P m = cross (b - a) (c - b)
  have hcorner : cornerCross P m = cross (b - a) (c - b) := by
    unfold cornerCross; rfl
  -- edgeThr y (m-1) = crossThreshold a b y  (edge m-1 goes vert(m-1) → vert m)
  have hedge1 : P.edgeThr y (m - 1) = crossThreshold a b y := by
    unfold LatticePolygon.edgeThr
    rw [sub_add_cancel]
  -- edgeThr y m = crossThreshold b c y  (edge m goes vert m → vert (m+1))
  have hedge2 : P.edgeThr y m = crossThreshold b c y := by
    unfold LatticePolygon.edgeThr; rfl
  rw [hcorner, hedge1, hedge2]
  have hkey := crossThreshold_gap_eq_cornerCross a b c y hba hbc hby
  have hpos1 : 0 < (a.2 - b.2) := by linarith
  have hpos2 : 0 < (c.2 - b.2) := by linarith
  have hprod : 0 < (a.2 - b.2) * (c.2 - b.2) := mul_pos hpos1 hpos2
  have hyb : 0 < y - b.2 := by linarith
  constructor
  · intro hcc
    -- cross (b-a)(c-b) > 0 ⟹ gap*prod > 0 ⟹ (since prod>0) gap > 0
    have hrhs : 0 < cross (b - a) (c - b) * (y - b.2) := mul_pos hcc hyb
    rw [← hkey] at hrhs
    -- hrhs : 0 < gap * prod ; with prod > 0 conclude gap > 0
    have hgap : 0 < crossThreshold b c y - crossThreshold a b y :=
      pos_of_mul_pos_left hrhs (le_of_lt hprod)
    linarith
  · intro hthr
    have hgap : 0 < crossThreshold b c y - crossThreshold a b y := by linarith
    have hlhs : 0 < (crossThreshold b c y - crossThreshold a b y) * ((a.2 - b.2) * (c.2 - b.2)) :=
      mul_pos hgap hprod
    rw [hkey] at hlhs
    -- hlhs : 0 < cross * (y-b.2) ; with (y-b.2)>0 conclude cross > 0
    exact pos_of_mul_pos_left hlhs (le_of_lt hyb)

/-- **Lex-lowest cone (unconditional).** At the lexicographically-lowest vertex `m`,
both incident *outgoing* vectors at `m` — the reversed incoming `vₘ₋₁ − vₘ` and the
outgoing `vₘ₊₁ − vₘ` — lie in the closed upper half-plane (`y ≥ 0`), and when one of
them is horizontal (`y = 0`) it points strictly to the right (`x > 0`). Equivalently:
both neighbours `vₘ₋₁, vₘ₊₁` sit in the half-open cone `U = {y > 0} ∪ {y = 0, x > 0}`
based at `vₘ`. This is the unconditional separation behind the convexity of the
lowest corner; it is the `cross`-side repackaging of `lex_lowest_edge_signs`. -/
lemma lex_lowest_neighbors_above (P : LatticePolygon) (hS : P.IsSimple) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1)) :
    0 ≤ (toReal (P.vert (m - 1)) - toReal (P.vert m)).2 ∧
    0 ≤ (toReal (P.vert (m + 1)) - toReal (P.vert m)).2 ∧
    ((toReal (P.vert (m - 1)) - toReal (P.vert m)).2 = 0 →
      0 < (toReal (P.vert (m - 1)) - toReal (P.vert m)).1) ∧
    ((toReal (P.vert (m + 1)) - toReal (P.vert m)).2 = 0 →
      0 < (toReal (P.vert (m + 1)) - toReal (P.vert m)).1) := by
  obtain ⟨ho, hi, ho0, hi0⟩ := lex_lowest_edge_signs P hS m hlex
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Prod.snd_sub] at hi ⊢; linarith
  · simp only [Prod.snd_sub] at ho ⊢; linarith
  · intro h; have := hi0 (by simp only [Prod.snd_sub] at h ⊢; linarith)
    simp only [Prod.fst_sub] at this ⊢; linarith
  · intro h; have := ho0 (by simp only [Prod.snd_sub] at h ⊢; linarith)
    simp only [Prod.fst_sub] at this ⊢; linarith

/-- **Corner cross at the lowest vertex as a single 2×2 determinant.** With the apex
`vₘ` as the base point, `cornerCross P m = cross (vₘ − vₘ₋₁) (vₘ₊₁ − vₘ)`. Writing
`p := vₘ₋₁ − vₘ` and `q := vₘ₊₁ − vₘ` (the two outgoing vectors of
`lex_lowest_neighbors_above`, both in the closed upper half-plane), this equals
`-cross p q = cross q p`. So `0 < cornerCross P m ↔ cross p q < 0`: the corner is
convex iff the outgoing neighbour `q` is *clockwise* from the incoming neighbour `p`.
This is the exact algebraic target that the global orientation must pin down. -/
lemma cornerCross_eq_neg_cross_neighbors (P : LatticePolygon) (m : ZMod P.n) :
    cornerCross P m =
      - cross (toReal (P.vert (m - 1)) - toReal (P.vert m))
              (toReal (P.vert (m + 1)) - toReal (P.vert m)) := by
  unfold cornerCross cross
  simp only [Prod.fst_sub, Prod.snd_sub]; ring

/-- **Parallel vectors in the lex-up cone are same-ray (one is a sub-multiple of the
other).** Two vectors `p, q` lying in the half-open *lex-up* cone — closed upper
half-plane `{y ≥ 0}` with the horizontal boundary trimmed to the positive `x`-axis
(`y = 0 → x > 0`) — that are parallel (`cross p q = 0`) point in the *same* direction:
the shorter of the two is `s • (the longer)` for some `s ∈ [0,1]`. (The cone is
"salient": it contains no pair of opposite rays, so collinear forces same-ray.) -/
lemma lex_up_parallel_sameray (p q : ℝ × ℝ)
    (hp2 : 0 ≤ p.2) (hq2 : 0 ≤ q.2)
    (hp0 : p.2 = 0 → 0 < p.1) (hq0 : q.2 = 0 → 0 < q.1)
    (hcr : cross p q = 0) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (q = s • p ∨ p = s • q) := by
  unfold cross at hcr
  rcases eq_or_lt_of_le hp2 with hp2e | hp2lt
  · -- p on the positive x-axis: forces q there too, compare x-coords
    have hp1 : 0 < p.1 := hp0 hp2e.symm
    have hq2z : q.2 = 0 := by
      have : p.1 * q.2 = 0 := by rw [← hp2e] at hcr; nlinarith [hcr]
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    have hq1 : 0 < q.1 := hq0 hq2z
    rcases le_total q.1 p.1 with hle | hle
    · refine ⟨q.1 / p.1, by positivity, by rw [div_le_one hp1]; exact hle, Or.inl ?_⟩
      ext
      · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
      · simp only [Prod.smul_snd, smul_eq_mul, hq2z, ← hp2e, mul_zero]
    · refine ⟨p.1 / q.1, by positivity, by rw [div_le_one hq1]; exact hle, Or.inr ?_⟩
      ext
      · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
      · simp only [Prod.smul_snd, smul_eq_mul, hq2z, ← hp2e, mul_zero]
  · -- p strictly above: compare y-coords
    rcases le_total q.2 p.2 with hle | hle
    · refine ⟨q.2 / p.2, by positivity, by rw [div_le_one hp2lt]; exact hle, Or.inl ?_⟩
      ext
      · simp only [Prod.smul_fst, smul_eq_mul]; field_simp; nlinarith [hcr]
      · simp only [Prod.smul_snd, smul_eq_mul]; field_simp
    · have hq2lt : 0 < q.2 := lt_of_lt_of_le hp2lt hle
      refine ⟨p.2 / q.2, by positivity, by rw [div_le_one hq2lt]; exact hle, Or.inr ?_⟩
      ext
      · simp only [Prod.smul_fst, smul_eq_mul]; field_simp; nlinarith [hcr]
      · simp only [Prod.smul_snd, smul_eq_mul]; field_simp

/-- **TASK 1 — the lowest corner is non-degenerate.** At the lex-lowest vertex `vₘ`
of a simple polygon the corner cross is nonzero: `cornerCross P m ≠ 0`. If it
vanished, the incoming and outgoing edge vectors `p = vₘ₋₁ − vₘ` and `q = vₘ₊₁ − vₘ`
would be parallel (`cross p q = 0`); but both lie in the *lex-up* cone
(`lex_lowest_neighbors_above`: closed upper half-plane, horizontal boundary trimmed to
positive `x`), so by `lex_up_parallel_sameray` they point in the *same* direction. The
shorter neighbour then lies on the longer edge: either `vₘ₊₁ ∈ edgeSeg(m−1)` or
`vₘ₋₁ ∈ edgeSeg(m)`. Combined with its own incident edge this puts it in
`edgeSeg(m−1) ∩ edgeSeg(m) = {vₘ}` (simplicity clause 3), forcing a neighbour to
coincide with `vₘ` — contradicting nondegeneracy. Geometrically: a collinear
backtrack at the lowest corner makes the two incident edges overlap, which a simple
(Jordan) boundary forbids. -/
lemma cornerCross_ne_zero_lex_lowest (P : LatticePolygon) (hS : P.IsSimple) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1)) :
    cornerCross P m ≠ 0 := by
  intro h0
  obtain ⟨hpa2, hqa2, hpa0, hqa0⟩ := lex_lowest_neighbors_above P hS m hlex
  have hccn := cornerCross_eq_neg_cross_neighbors P m
  set a := toReal (P.vert (m - 1)) with ha
  set b := toReal (P.vert m) with hb
  set c := toReal (P.vert (m + 1)) with hc
  have hcr : cross (a - b) (c - b) = 0 := by
    rw [hccn] at h0; linarith [h0]
  obtain ⟨s, hs0, hs1, hcase⟩ :=
    lex_up_parallel_sameray (a - b) (c - b) hpa2 hqa2 hpa0 hqa0 hcr
  -- a convex-combination point of `segment x z` with offset given by a sub-multiple
  have segmem : ∀ (x y z : ℝ × ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      (y - z = t • (x - z)) → y ∈ segment ℝ x z := by
    intro x y z t ht0 ht1 hh
    refine ⟨t, 1 - t, ht0, by linarith, by ring, ?_⟩
    have : y = t • (x - z) + z := by rw [← hh]; abel
    rw [this]; simp [smul_sub, sub_smul, one_smul]; abel
  have he : (m - 1) + 1 = m := by ring
  rcases hcase with hcase | hcase
  · -- `q = s • p`: outgoing neighbour `c = vₘ₊₁` lies on the incoming edge
    have hseg1 : c ∈ segment ℝ a b := segmem a c b s hs0 hs1 hcase
    have hmem1 : c ∈ P.edgeSeg (m - 1) := by
      rw [LatticePolygon.edgeSeg, he, ← hb]; exact hseg1
    have hmem2 : c ∈ P.edgeSeg m := by
      rw [LatticePolygon.edgeSeg]; exact right_mem_segment ℝ _ _
    have hint : c ∈ P.edgeSeg (m - 1) ∩ P.edgeSeg ((m - 1) + 1) := by
      rw [he]; exact ⟨hmem1, hmem2⟩
    rw [hS.2.2 (m - 1), he] at hint
    have hcb : P.vert (m + 1) = P.vert m := toReal_injective hint
    exact hS.1 m hcb.symm
  · -- `p = s • q`: incoming neighbour `a = vₘ₋₁` lies on the outgoing edge
    have hseg1 : a ∈ segment ℝ c b := segmem c a b s hs0 hs1 hcase
    have hmem1 : a ∈ P.edgeSeg m := by
      rw [LatticePolygon.edgeSeg, ← hb, ← hc, segment_symm ℝ b c]; exact hseg1
    have hmem2 : a ∈ P.edgeSeg (m - 1) := by
      rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _
    have hint : a ∈ P.edgeSeg (m - 1) ∩ P.edgeSeg ((m - 1) + 1) := by
      rw [he]; exact ⟨hmem2, hmem1⟩
    rw [hS.2.2 (m - 1), he] at hint
    have hab : P.vert (m - 1) = P.vert m := toReal_injective hint
    exact hS.1 (m - 1) (by rw [he]; exact hab)

/-- **The reversed polygon.** Same vertex set, opposite traversal order: vertex `i`
of `reverseP P` is `vₘ` with `m = −i`. Reversing the boundary orientation negates
both the shoelace (signed area) and the corner cross at every vertex. This is the
orientation-symmetry workhorse: it lets one reduce sign statements for negatively
oriented polygons to the positively oriented case, and pins down the *sign
correspondence* `sign(cornerCross P m) = sign(P.shoelace)`. -/
def reverseP (P : LatticePolygon) : LatticePolygon where
  n := P.n
  pos := P.pos
  vert := fun i => P.vert (-i)

@[simp] lemma reverseP_n (P : LatticePolygon) : (reverseP P).n = P.n := rfl

@[simp] lemma reverseP_vert (P : LatticePolygon) (i : ZMod P.n) :
    (reverseP P).vert i = P.vert (-i) := rfl

/-- **Reversal negates the signed area.** `shoelace (reverseP P) = − shoelace P`:
traversing the boundary the other way flips the sign of every fan triangle. -/
lemma reverseP_shoelace (P : LatticePolygon) :
    (reverseP P).shoelace = - P.shoelace := by
  have hsum : (∑ x : ZMod P.n, cross (toReal (P.vert (-x))) (toReal (P.vert (-(x + 1)))))
      = - ∑ i, cross (toReal (P.vert i)) (toReal (P.vert (i + 1))) := by
    have h1 : (∑ x : ZMod P.n, cross (toReal (P.vert (-x))) (toReal (P.vert (-(x + 1)))))
        = ∑ i : ZMod P.n, cross (toReal (P.vert i)) (toReal (P.vert (i - 1))) := by
      rw [← Equiv.sum_comp (Equiv.neg (ZMod P.n))
        (fun x => cross (toReal (P.vert x)) (toReal (P.vert (x - 1))))]
      apply Finset.sum_congr rfl; intro i _
      simp only [Equiv.neg_apply]
      have : -(i + 1) = -i - 1 := by ring
      rw [this]
    rw [h1]
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n))
      (fun i => cross (toReal (P.vert i)) (toReal (P.vert (i - 1))))]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [Equiv.coe_addRight]
    have : i + 1 - 1 = i := by ring
    rw [this]
    unfold cross; ring
  show (∑ x, cross (toReal (P.vert (-x))) (toReal (P.vert (-(x + 1))))) / 2 = - P.shoelace
  rw [hsum, neg_div]
  rfl

/-- **The fan / signed-area identity (apex translation invariance).** For *any*
fixed apex `o`, twice the shoelace equals the sum over edges of the signed area of
the fan triangle `(o, vᵢ, vᵢ₊₁)`:
`2·shoelace = ∑ᵢ cross(vᵢ − o, vᵢ₊₁ − o)`.
The `o`-dependent contributions telescope to zero around the cyclic edge sum
(`∑ᵢ eᵢ = 0`), so the value is independent of the apex. Taking `o = vₖ` a vertex
makes the two edge-terms incident to `vₖ` vanish, leaving a fan over the remaining
edges — the geometric basis of the convex-vertex existence argument. -/
theorem two_shoelace_fan_apex (P : LatticePolygon) (o : ℝ × ℝ) :
    (∑ i, cross (toReal (P.vert i) - o) (toReal (P.vert (i + 1)) - o)) = 2 * P.shoelace := by
  have hcross : ∀ i, cross (toReal (P.vert i) - o) (toReal (P.vert (i + 1)) - o)
      = cross (toReal (P.vert i)) (toReal (P.vert (i+1)))
        - (cross o (toReal (P.vert (i+1))) - cross o (toReal (P.vert i))) := by
    intro i; unfold cross; simp only [Prod.fst_sub, Prod.snd_sub]; ring
  simp only [hcross]
  rw [Finset.sum_sub_distrib]
  have htel : (∑ i, (cross o (toReal (P.vert (i+1))) - cross o (toReal (P.vert i)))) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod P.n)) _ _ (fun i => rfl)
  rw [htel, sub_zero]
  unfold LatticePolygon.shoelace; ring

/-- **The fan at a vertex apex `vₖ`.** Specialising `two_shoelace_fan_apex` to the
apex `o = vₖ`: the two edge-terms incident to `vₖ` (namely `i = k` and `i = k−1`)
vanish because `vₖ − vₖ = 0`, so `2·shoelace` equals the fan sum over the remaining
`n − 2` edges. Each surviving term `cross(vᵢ − vₖ, vᵢ₊₁ − vₖ)` is twice the signed
area of the triangle `(vₖ, vᵢ, vᵢ₊₁)`. -/
theorem two_shoelace_fan_vertex (P : LatticePolygon) (k : ZMod P.n) :
    (∑ i, cross (toReal (P.vert i) - toReal (P.vert k))
                (toReal (P.vert (i + 1)) - toReal (P.vert k))) = 2 * P.shoelace :=
  two_shoelace_fan_apex P (toReal (P.vert k))

/-- **A positively-oriented fan triangle exists.** If `0 < shoelace`, then for the
fan from any apex `vₖ` some edge `(i, i+1)` spans a strictly positively-oriented
triangle `cross(vᵢ − vₖ, vᵢ₊₁ − vₖ) > 0` (a nonempty positive part of a sum with
positive total). Taking `o = vₖ` extreme (lex-lowest) makes all fan vectors lie in
the closed upper half-plane, the starting point for forcing a convex corner. -/
theorem exists_pos_fan_term (P : LatticePolygon) (horient : P.PositivelyOriented)
    (k : ZMod P.n) :
    ∃ i, 0 < cross (toReal (P.vert i) - toReal (P.vert k))
                   (toReal (P.vert (i + 1)) - toReal (P.vert k)) := by
  by_contra hcon
  push Not at hcon
  have hsum : (∑ i, cross (toReal (P.vert i) - toReal (P.vert k))
      (toReal (P.vert (i + 1)) - toReal (P.vert k))) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => hcon i)
  rw [two_shoelace_fan_vertex P k] at hsum
  have : (0:ℝ) < 2 * P.shoelace := by unfold LatticePolygon.PositivelyOriented at horient; linarith
  linarith

/-- **All fan vectors from the lex-lowest apex lie in the closed upper half-plane.**
With apex `vₘ` the lex-lowest vertex, every vector `vⱼ − vₘ` has non-negative
`y`-component (`lex_lowest_all_above`). Hence the whole fan
`{vⱼ − vₘ}` lives in `{y ≥ 0}`: the supporting horizontal line through `vₘ` keeps the
entire polygon weakly above. This is the "extreme vertex ⟹ one-sided fan" fact:
combined with `two_shoelace_fan_vertex` it constrains the signs of the fan triangles
(each `cross(vᵢ−vₘ, vᵢ₊₁−vₘ)` is the determinant of two upper-half-plane vectors). -/
lemma fan_vectors_upper_halfplane (P : LatticePolygon) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (j : ZMod P.n) :
    0 ≤ (toReal (P.vert j) - toReal (P.vert m)).2 := by
  have := lex_lowest_all_above P m hlex j
  simp only [toReal, Prod.snd_sub] at this ⊢; linarith

/-! ### Angular preorder on the closed upper half-plane

For vectors in the closed upper half-plane `{y ≥ 0}` the sign of `cross u v`
measures angular order: `cross u v ≥ 0` means `v` is counter-clockwise from (or
equal to) `u`, i.e. `angle u ≤ angle v` within `[0, π]`. This makes the relation
`u ≼ v := 0 ≤ cross u v` a *total preorder* on the (nonzero) upper half-plane.
The two foundational facts are **transitivity** (proved by the Plücker/Grassmann
identity `cross u w · ‖v‖² = cross u v · (v·w) + cross v w · (v·u)` together with
the half-plane sign constraints) and **totality** (immediate from
`cross v u = - cross u v`). These are the reusable backbone of the convex-corner
argument: the fan vectors at the lex-lowest apex all lie in `{y ≥ 0}`, hence are
angularly sortable, and the chain endpoints `vₘ₋₁, vₘ₊₁` inherit the order. -/

/-- **`cross` is antisymmetric.** `cross v u = - cross u v`; hence the angular
relation `0 ≤ cross · ·` is total on any set of vectors. -/
lemma cross_swap (u v : ℝ × ℝ) : cross v u = - cross u v := by
  simp only [cross]; ring

/-- **A vector points into the open angular sector `[0, π)`.** `UpperHalfOpen w`
holds when `w` lies in the closed upper half-plane *and* off the closed negative
`x`-axis, i.e. its angle is in `[0, π)` (excluding the direction `(-1,0)`). On this
sector the `cross`-sign relation `0 ≤ cross · ·` is a genuine *strict* order: no two
distinct vectors are mutually `≼`. At the lex-lowest apex every fan vector
`vⱼ − vₘ` (`j ≠ m`) has this property — a vertex at the same height as `vₘ` sits
strictly to its right (`lex_lowest_x_gap`), so the `(-1,0)` direction is unused. -/
def UpperHalfOpen (w : ℝ × ℝ) : Prop := 0 ≤ w.2 ∧ (0 < w.2 ∨ 0 < w.1)

/-- **Strict angular transitivity on the sector `[0, π)`.** If `u, v, w` are all in
`UpperHalfOpen` (angles in `[0, π)`), `cross u v ≥ 0` and `cross v w > 0`, then
`cross u w > 0`. The exclusion of the `(-1,0)` direction (built into
`UpperHalfOpen`) is exactly what makes the angular order strict — without it
`(1,0)` and `(-1,0)` would be mutually non-strict. This is the engine that turns a
single strict angular step in the fan chain into a strict ordering of the chain
endpoints. The proof uses the deterministic determinant identity
`v.2·cross u w = w.2·cross u v + u.2·cross v w` (case `v.2 > 0`) and a direct
reduction when `v.2 = 0` (then `v.1 > 0`, forcing `u.2 = 0`, `0 < w.2`). -/
lemma cross_trans_upperHalfOpen_strict (u v w : ℝ × ℝ)
    (hu : UpperHalfOpen u) (hv : UpperHalfOpen v) (hw : UpperHalfOpen w)
    (h1 : 0 ≤ cross u v) (h2 : 0 < cross v w) : 0 < cross u w := by
  obtain ⟨hu2, hu⟩ := hu; obtain ⟨hv2, hv⟩ := hv; obtain ⟨hw2, hw⟩ := hw
  simp only [cross] at *
  -- the determinant identity `v.2·cross u w = w.2·cross u v + u.2·cross v w`
  have id2 : v.2 * (u.1 * w.2 - u.2 * w.1)
      = w.2 * (u.1 * v.2 - u.2 * v.1) + u.2 * (v.1 * w.2 - v.2 * w.1) := by ring
  rcases eq_or_lt_of_le hv2 with hv2' | hv2'
  · -- v.2 = 0 : `UpperHalfOpen v` forces v.1 > 0
    have hv2z : v.2 = 0 := hv2'.symm
    have hv1 : 0 < v.1 := by
      rcases hv with h | h
      · exact absurd hv2z (ne_of_gt h)
      · exact h
    -- from `cross u v ≥ 0`: `-u.2·v.1 ≥ 0` ⟹ u.2 = 0 ; from `cross v w > 0`: `v.1·w.2 > 0`
    have hu2z : u.2 = 0 := by
      have : 0 ≤ -(u.2 * v.1) := by rw [hv2z] at h1; linarith
      have hle : u.2 * v.1 ≤ 0 := by linarith
      have : u.2 ≤ 0 := nonpos_of_mul_nonpos_left hle hv1
      linarith
    have hw2p : 0 < w.2 := by
      rw [hv2z] at h2; nlinarith
    have hu1 : 0 < u.1 := by
      rcases hu with h | h
      · exact absurd hu2z (ne_of_gt h)
      · exact h
    rw [hu2z]; nlinarith [mul_pos hu1 hw2p]
  · -- v.2 > 0 : use `id2`, split on whether u.2 vanishes
    rcases eq_or_lt_of_le hu2 with hu2' | hu2'
    · -- u.2 = 0, so u.1 > 0 from `UpperHalfOpen u`; goal becomes `0 < u.1·w.2`
      have hu2z : u.2 = 0 := hu2'.symm
      have huc : 0 < u.1 := by
        rcases hu with h | h
        · exact absurd hu2z (ne_of_gt h)
        · exact h
      rw [hu2z]
      -- goal `0 < u.1·w.2 - 0·w.1`; with v.2 > 0, need w.2 > 0
      have hw2p : 0 < w.2 := by
        rcases eq_or_lt_of_le hw2 with hw2z | hw2p
        · -- w.2 = 0 ⟹ w.1 > 0 (UpperHalfOpen) ⟹ cross v w = -v.2·w.1 < 0, contra h2
          exfalso
          have hw1 : 0 < w.1 := by
            rcases hw with hwc | hwc
            · exact absurd hw2z.symm (ne_of_gt hwc)
            · exact hwc
          rw [← hw2z] at h2; nlinarith [mul_pos hv2' hw1]
        · exact hw2p
      nlinarith [mul_pos huc hw2p]
    · nlinarith [id2, mul_pos hu2' h2, mul_nonneg hw2 h1, hv2']

/-- **Ear-triangle area is half the clipped corner cross.** The ear triangle
`(vₘ, vₘ₊₁, v₀)` cut off by `deleteLast` is the corner at the *last* vertex
`vₘ₊₁ = v_{n-1}` (here `n = m+2`, so `(m+1)+1 = 0` cyclically and `(m+1)-1 = m`).
Its signed area is exactly `½·cornerCross P (m+1)`. This is the algebraic hinge
that turns the proven area additivity into a statement about the clipped corner. -/
lemma earTri_shoelace_eq_cornerCross (P : LatticePolygon) (m : ℕ) (hm : P.n = m + 2) :
    (earTri P m hm).shoelace = cornerCross P ((m : ZMod P.n) + 1) / 2 := by
  rw [earTri_shoelace P m hm]
  unfold cornerCross cross
  have e1 : ((m : ZMod P.n) + 1) - 1 = (m : ZMod P.n) := by ring
  have e2 : ((m : ZMod P.n) + 1) + 1 = (0 : ZMod P.n) := by
    have hz : ((m + 2 : ℕ) : ZMod P.n) = 0 := by rw [← hm]; exact ZMod.natCast_self P.n
    push_cast at hz; linear_combination hz
  rw [e1, e2]
  simp only [Prod.fst_sub, Prod.snd_sub]; ring

/-- **Clipped corner cross = twice the area drop under ear-clipping** (non-circular
area bridge). Combining `shoelace_eq_deleteLast_add_earTri` with
`earTri_shoelace_eq_cornerCross`, the corner cross at the clipped (last) vertex
`vₘ₊₁` equals `2·(shoelace P − shoelace (deleteLast P))`. Hence
`0 < cornerCross P (m+1) ↔ shoelace (deleteLast P) < shoelace P`: the last corner
is convex iff clipping its ear strictly *decreases* the signed area. This converts
the corner-convexity question at the clipped vertex into a pure signed-area
comparison, with no winding/cross-section machinery. -/
lemma cornerCross_clip_eq_shoelace_drop (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ)
    (hm : P.n = m + 2) :
    cornerCross P ((m : ZMod P.n) + 1) = 2 * (P.shoelace - (deleteLast P h).shoelace) := by
  have hadd := shoelace_eq_deleteLast_add_earTri P h m hm
  rw [earTri_shoelace_eq_cornerCross P m hm] at hadd
  linarith

/-- **Unique-lowest spanning set.** If `m` is lex-lowest, is the **unique**
minimum-height vertex, and both neighbours lie strictly above `vₘ`, then at any
generic height `y` strictly inside the lowest unit band the spanning edges are
**exactly** `{m-1, m}` (the incoming down-edge and the outgoing up-edge at `m`). -/
lemma spanningSet_unique_lowest (P : LatticePolygon) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (huniq : ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert m)).2 → j = m)
    (hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2)
    (hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2)
    (y : ℝ) (hlo : (toReal (P.vert m)).2 < y) (hhi : y < (toReal (P.vert m)).2 + 1) :
    P.spanningSet y = {m - 1, m} := by
  classical
  ext i
  rw [spanning_at_lowest_band P m hlex y hlo hhi]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨hi, _⟩ | ⟨hi1, _⟩)
    · exact Or.inr (huniq i hi)
    · have : i + 1 = m := huniq (i + 1) hi1
      left; rw [← this]; ring
  · rintro (rfl | rfl)
    · refine Or.inr ⟨?_, ?_⟩
      · rw [sub_add_cancel]
      · exact ne_of_gt hba
    · refine Or.inl ⟨rfl, ?_⟩
      exact ne_of_gt hbc

/-- **Lex-lowest x-gap.** Any *other* vertex `k` sitting at the same (minimum)
height as the lex-lowest vertex `m` has abscissa at least `xₘ + 1`: among the
floor vertices, `m` is the strict left-most, and lattice abscissae are integers, so
the gap is a full unit. This is the quantitative separation that makes `m`'s two
incident crossings the unique left-most pair in the lowest band. -/
lemma lex_lowest_x_gap (P : LatticePolygon) (hS : P.IsSimple) (m k : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (hkm : k ≠ m) (hheq : (toReal (P.vert k)).2 = (toReal (P.vert m)).2) :
    (toReal (P.vert m)).1 + 1 ≤ (toReal (P.vert k)).1 := by
  have hne : P.vert k ≠ P.vert m := fun h => hkm (vert_injective P hS h)
  have hl := hlex k
  rw [Prod.Lex.toLex_le_toLex] at hl
  simp only [toReal] at hheq ⊢
  have hyeq : (P.vert m).2 = (P.vert k).2 := by exact_mod_cast hheq.symm
  rcases hl with h | ⟨_, hx⟩
  · exact absurd hyeq (ne_of_lt (by exact_mod_cast h))
  · have hxlt : (P.vert m).1 < (P.vert k).1 := by
      rcases lt_or_eq_of_le hx with h | h
      · exact h
      · exact absurd (Prod.ext h.symm hyeq.symm) hne
    have hZ : (P.vert m).1 + 1 ≤ (P.vert k).1 := Int.add_one_le_iff.mpr hxlt
    exact_mod_cast hZ

/-- **STEP 1 — Strict open-half-plane support at the lex-lowest apex.** At the
lexicographically-lowest vertex `m` there is a single linear functional
`d := (δ, 1)` (any small `0 < δ < 1`) that is **strictly positive** on *every*
other fan vector `wⱼ := vⱼ − vₘ` (`j ≠ m`):
`0 < δ·(wⱼ).1 + (wⱼ).2`. This upgrades the *closed* upper-half-plane bound
(`fan_vectors_upper_halfplane`) to a strict **open** half-plane `{⟨·, d⟩ > 0}`
containing all the `wⱼ`. Reason: if `(wⱼ).2 = 0` then `j` sits at the floor height
so `lex_lowest_x_gap` forces `(wⱼ).1 ≥ 1 > 0`; if `(wⱼ).2 > 0` the height is an
integer `≥ 1`, so a small enough `δ` (smaller than `1/(max|x|+1)`) keeps the sum
positive. Choosing `δ = 1/(C+1)` with `C` a uniform bound on `|(wⱼ).1|` over the
finite vertex set works for all `j` at once. The fan vectors thus have angles in an
*open* interval of width `< π` — totally ordered by the angular preorder, no wrap. -/
lemma lex_lowest_strict_support (P : LatticePolygon) (hS : P.IsSimple) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ j, j ≠ m →
      0 < δ * (toReal (P.vert j) - toReal (P.vert m)).1
            + (toReal (P.vert j) - toReal (P.vert m)).2 := by
  obtain ⟨C, hC⟩ := Finset.exists_le
    (Finset.univ.image (fun j : ZMod P.n => |(toReal (P.vert j) - toReal (P.vert m)).1|))
  simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index] at hC
  have hCval : ∀ j : ZMod P.n, |(toReal (P.vert j) - toReal (P.vert m)).1| ≤ C :=
    fun j => hC _ j rfl
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hCval m)
  refine ⟨1 / (C + 2), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  · intro j hj
    set w := toReal (P.vert j) - toReal (P.vert m) with hw
    have hy : 0 ≤ w.2 := fan_vectors_upper_halfplane P m hlex j
    rcases eq_or_lt_of_le hy with hy0 | hy0
    · -- w.2 = 0 : floor-height vertex, x-gap gives w.1 ≥ 1
      have hheq : (toReal (P.vert j)).2 = (toReal (P.vert m)).2 := by
        simp only [hw, Prod.snd_sub] at hy0; linarith
      have hx1 : (toReal (P.vert m)).1 + 1 ≤ (toReal (P.vert j)).1 :=
        lex_lowest_x_gap P hS m j hlex hj hheq
      have hwx1 : 1 ≤ w.1 := by simp only [hw, Prod.fst_sub]; linarith
      simp only [← hy0]
      linarith [mul_pos (show (0:ℝ) < 1/(C+2) by positivity)
        (show (0:ℝ) < w.1 by linarith)]
    · -- w.2 > 0 : integer height ≥ 1, small δ keeps the sum positive
      have hyZ : (1:ℝ) ≤ w.2 := by
        have hlt : (toReal (P.vert m)).2 < (toReal (P.vert j)).2 := by
          simp only [hw, Prod.snd_sub] at hy0 ⊢; linarith
        simp only [toReal] at hlt
        have hZ : (P.vert m).2 < (P.vert j).2 := by exact_mod_cast hlt
        have hZ1 : (P.vert m).2 + 1 ≤ (P.vert j).2 := by omega
        have hR : ((P.vert m).2 :ℝ) + 1 ≤ ((P.vert j).2 :ℝ) := by exact_mod_cast hZ1
        simp only [hw, Prod.snd_sub, toReal]; linarith
      have hxb : |w.1| ≤ C := hCval j
      have hbound : (1/(C+2)) * w.1 ≥ - (1/(C+2)) * C := by
        have : -C ≤ w.1 := by rw [abs_le] at hxb; linarith
        nlinarith [show (0:ℝ) < 1/(C+2) by positivity]
      have hlt1 : (1/(C+2)) * C < 1 := by
        rw [div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
      linarith

/-- **STEP 2a — Strict angular transitivity in a functional-defined open half-plane.**
Generalises `cross_trans_upperHalfOpen_strict` from the fixed `(-1,0)`-excluding
sector to *any* open half-plane `{w : 0 < δ·w.1 + w.2}` cut out by the functional
`d = (δ, 1)` with `0 < δ`. If `u, v, w` all lie strictly in this half-plane,
`cross u v ≥ 0` and `cross v w > 0`, then `cross u w > 0`. The proof applies the
volume-preserving shear `S w := (w.1, δ·w.1 + w.2)` (determinant `1`, so
`cross (S a) (S b) = cross a b`), which carries the half-plane onto the standard
open upper half-plane `{y > 0} ⊆ UpperHalfOpen`. Hence the fan vectors at the
lex-lowest apex (all strictly inside the support half-plane by
`lex_lowest_strict_support`) are *totally and strictly* angularly ordered by
`u ≼ v := 0 ≤ cross u v` — no boundary wrap. -/
lemma cross_trans_strict_support (δ : ℝ) (_hδ : 0 < δ) (u v w : ℝ × ℝ)
    (hu : 0 < δ * u.1 + u.2) (hv : 0 < δ * v.1 + v.2) (hw : 0 < δ * w.1 + w.2)
    (h1 : 0 ≤ cross u v) (h2 : 0 < cross v w) : 0 < cross u w := by
  have key : ∀ a b : ℝ × ℝ,
      cross (a.1, δ * a.1 + a.2) (b.1, δ * b.1 + b.2) = cross a b := by
    intro a b; simp only [cross]; ring
  have hU : UpperHalfOpen (u.1, δ * u.1 + u.2) := ⟨le_of_lt hu, Or.inl hu⟩
  have hV : UpperHalfOpen (v.1, δ * v.1 + v.2) := ⟨le_of_lt hv, Or.inl hv⟩
  have hW : UpperHalfOpen (w.1, δ * w.1 + w.2) := ⟨le_of_lt hw, Or.inl hw⟩
  have := cross_trans_upperHalfOpen_strict _ _ _ hU hV hW
    (by rw [key]; exact h1) (by rw [key]; exact h2)
  rwa [key] at this

/-- **STEP 2a (mirror) — strict-first angular transitivity in the support half-plane.**
The mirror of `cross_trans_strict_support`: a *strict* first step `cross u v > 0`
followed by a *weak* second step `cross v w ≥ 0` still yields `cross u w > 0`. Proved
from the original via the antisymmetry `cross_swap` (totality of the order): if
`cross u w ≤ 0` then `0 ≤ cross w u`, and chaining `(w, u, v)` would force
`cross v w < 0`. Together the two transitivity lemmas make `≼` a genuine strict
total order on the support half-plane. -/
lemma cross_trans_strict_support' (δ : ℝ) (hδ : 0 < δ) (u v w : ℝ × ℝ)
    (hu : 0 < δ * u.1 + u.2) (hv : 0 < δ * v.1 + v.2) (hw : 0 < δ * w.1 + w.2)
    (h1 : 0 < cross u v) (h2 : 0 ≤ cross v w) : 0 < cross u w := by
  by_contra hcon
  push Not at hcon
  have hwu : 0 ≤ cross w u := by have := cross_swap u w; linarith
  have hwv : 0 < cross w v := cross_trans_strict_support δ hδ w u v hw hu hv hwu h1
  have := cross_swap v w; linarith

/-- **STEP 1 — the determinant-1 shear preserves `cross`.** The linear shear
`S(x, y) = (x, c·x + y)` has determinant `1`; consequently it preserves the
signed area `cross`: `cross (S u) (S v) = cross u v` for all `u, v`. This is the
volume-preserving change of coordinates used to send the support functional
`d = (δ, 1)` to the vertical axis, carrying the open support half-plane
`{δ·x + y > 0}` onto the standard open upper half-plane `{y > 0}` while leaving
every fan triangle's signed area (and hence the whole shoelace) unchanged. -/
lemma cross_shear_invariant (c : ℝ) (u v : ℝ × ℝ) :
    cross (u.1, c * u.1 + u.2) (v.1, c * v.1 + v.2) = cross u v := by
  simp only [cross]; ring

/-- **STEP 1 (fan reduction) — after the support shear the lex-lowest fan lies in
the OPEN upper half-plane.** Take the support slope `δ` from
`lex_lowest_strict_support` (so every fan vector `wⱼ := vⱼ − vₘ`, `j ≠ m`, has
`0 < δ·(wⱼ).1 + (wⱼ).2`). The shear `S(x,y) = (x, δ·x + y)` then sends each `wⱼ`
strictly into `{y > 0}`: `0 < (S wⱼ).2`. By `cross_shear_invariant` the shear
fixes every `cross`, so the angular order and the fan shoelace are untouched — the
problem is reduced to a simple chain genuinely inside the open upper half-plane. -/
lemma lex_lowest_fan_upper_open (P : LatticePolygon) (hS : P.IsSimple) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1)) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ j, j ≠ m →
        0 < δ * (toReal (P.vert j) - toReal (P.vert m)).1
              + (toReal (P.vert j) - toReal (P.vert m)).2) ∧
      (∀ u v : ℝ × ℝ,
        cross (u.1, δ * u.1 + u.2) (v.1, δ * v.1 + v.2) = cross u v) := by
  obtain ⟨δ, hδ, _, hsupp⟩ := lex_lowest_strict_support P hS m hlex
  exact ⟨δ, hδ, hsupp, fun u v => cross_shear_invariant δ u v⟩

/-- **The `cornerCross` at the apex *is* the chain-endpoint cross product.** Writing
the fan vectors `wⱼ := vⱼ − vₘ`, the corner cross at the lex-lowest apex equals
`cross (w₍ₘ₊₁₎) (w₍ₘ₋₁₎)` — the cross product of the *first* fan vector
(`w₍ₘ₊₁₎ = vₘ₊₁ − vₘ`, the outgoing neighbour, i.e. chain endpoint `w₀`) and the
*last* fan vector (`w₍ₘ₋₁₎ = vₘ₋₁ − vₘ`, the incoming neighbour, chain endpoint `wₖ`).
This is the bare algebraic restatement that turns the orientation/sign question at
the apex into the `fan_sign` question "`0 ≤ cross w₀ wₖ`" for the angularly-ordered
boundary chain. -/
lemma cornerCross_eq_cross_fan_endpoints (P : LatticePolygon) (m : ZMod P.n) :
    cornerCross P m =
      cross (toReal (P.vert (m + 1)) - toReal (P.vert m))
            (toReal (P.vert (m - 1)) - toReal (P.vert m)) := by
  unfold cornerCross cross; simp only [Prod.fst_sub, Prod.snd_sub]; ring

/-- **STEP 3 (sign assembly) — weak `fan_sign` upgrades to the strict corner sign.**
At the lex-lowest apex of a *simple* polygon, the corner cross is *non-zero*
(`cornerCross_ne_zero_lex_lowest`, the strict third simplicity clause rules out a
collinear/antiparallel apex corner). Hence the WEAK orientation inequality
`0 ≤ cornerCross P m` (the discrete-Umlaufsatz `fan_sign` content:
`0 ≤ cross w₀ wₖ` for the boundary chain) immediately upgrades to the STRICT
`0 < cornerCross P m`. This isolates the entire remaining geometric difficulty into
the single weak inequality `hweak`. -/
lemma cornerCross_pos_of_weak (P : LatticePolygon) (hS : P.IsSimple) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (hweak : 0 ≤ cornerCross P m) :
    0 < cornerCross P m :=
  lt_of_le_of_ne hweak (Ne.symm (cornerCross_ne_zero_lex_lowest P hS m hlex))

/-- **STEP 2 (the `fan_sign` content, weak form) as an explicit hypothesis.** The
*only* remaining purely-geometric input to the lowest-vertex orientation theorem.
For the boundary chain `w₀,…,wₖ` (with `w₀ := vₘ₊₁ − vₘ`, `wₖ := vₘ₋₁ − vₘ`,
the interior vertices the remaining `vⱼ − vₘ`) which, after the determinant-`1`
support shear (`lex_lowest_fan_upper_open`), is a SIMPLE chain lying in the OPEN
upper half-plane with positive fan shoelace `∑ cross(wᵢ,wᵢ₊₁) = 2·shoelace > 0`,
the *weak* discrete Umlaufsatz holds: `0 ≤ cross w₀ wₖ`. Equivalently
`0 ≤ cornerCross P m` by `cornerCross_eq_cross_fan_endpoints`.

Validated by exhaustive numeric search over simple CCW chains in the open upper
half-plane (`< 0` never occurs; only `= 0`, which the strict simplicity clause then
excludes via `cornerCross_pos_of_weak`). The standard proof is the splice
induction: every such chain with `k ≥ 2` admits an *interior* vertex whose removal
keeps the chain simple, in the open upper half-plane, with positive shoelace, and
fixes both endpoints `w₀, wₖ`; the base `k = 1` gives `cross w₀ w₁ = 2·shoelace > 0`.
The endpoints are preserved by every splice, so `cross w₀ wₖ` is unchanged down to
the base. -/
def FanSignWeak : Prop :=
  ∀ (P : LatticePolygon), P.IsSimple → P.PositivelyOriented → ∀ m : ZMod P.n,
    (∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1)) →
    0 ≤ cornerCross P m

/-- **Unique-lowest cross-section value.** In the unique-min-height configuration,
at a generic height `y` in the lowest band the cross-section value
`∫ winding(·,y)` is exactly the **signed gap** `edgeThr y m − edgeThr y (m-1)`
between the two crossings of `m`'s outgoing up-edge and incoming down-edge. -/
lemma crossSection_unique_lowest (P : LatticePolygon) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (huniq : ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert m)).2 → j = m)
    (hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2)
    (hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2)
    (y : ℝ) (hlo : (toReal (P.vert m)).2 < y) (hhi : y < (toReal (P.vert m)).2 + 1)
    (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    (∫ x, (P.winding (x, y) : ℝ)) = P.edgeThr y m - P.edgeThr y (m - 1) := by
  have hne : m - 1 ≠ m := by
    intro h
    have : (toReal (P.vert (m - 1))).2 = (toReal (P.vert m)).2 := by rw [h]
    linarith
  have hset : (Finset.univ.filter fun i =>
      ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)) = {m - 1, m} := by
    have := spanningSet_unique_lowest P m hlex huniq hba hbc y hlo hhi
    unfold LatticePolygon.spanningSet at this
    rw [this]
  rw [crossSection_value_two_spanning P y hgen (m - 1) m hne hset]
  -- evaluate the two `if` signs and identify thresholds with edgeThr
  have hsign1 : ¬ (y < (toReal (P.vert ((m - 1) + 1))).2) := by
    rw [sub_add_cancel]; exact not_lt.mpr (le_of_lt hlo)
  have hm1ne : (toReal (P.vert (m + 1))).2 ≠ (toReal (P.vert m)).2 := ne_of_gt hbc
  have hsign2 : y < (toReal (P.vert (m + 1))).2 :=
    lowest_band_above_of_ne_min P m hlex y hhi (m + 1) hm1ne
  rw [if_neg hsign1, if_pos hsign2]
  simp only [LatticePolygon.edgeThr, sub_add_cancel]
  ring

/-- **Above the floor means at least a unit above.** At the lex-lowest vertex `m`,
any vertex `k` not at the floor height `yₘ` has height `≥ yₘ + 1` (integer heights,
floor is the global minimum). -/
lemma lex_lowest_height_gap (P : LatticePolygon) (m k : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (hne : (toReal (P.vert k)).2 ≠ (toReal (P.vert m)).2) :
    (toReal (P.vert m)).2 + 1 ≤ (toReal (P.vert k)).2 := by
  have hmin := lex_lowest_all_above P m hlex k
  simp only [toReal] at *
  have hlt : ((P.vert m).2 : ℝ) < ((P.vert k).2 : ℝ) := lt_of_le_of_ne hmin (Ne.symm hne)
  have hZ : (P.vert m).2 < (P.vert k).2 := by exact_mod_cast hlt
  have hZ1 : (P.vert m).2 + 1 ≤ (P.vert k).2 := hZ
  exact_mod_cast hZ1

/-- **Lowest-band crossings separate at `xₘ + ½`.** At the lex-lowest vertex `m`,
for a generic band height `y` close enough to `yₘ`
(`(∑ⱼ|Δxⱼ|)·(y−yₘ) < ½`), the two crossings at `m` (edges `m−1` and `m`) lie left
of `xₘ + ½`, while every *other* spanning crossing lies strictly right of it. So
`m−1` and `m` are exactly the two left-most crossings of the lowest band. -/
lemma lowest_band_thresholds_separate (P : LatticePolygon) (hS : P.IsSimple) (m : ZMod P.n)
    (hlex : ∀ j, toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1))
    (hba : (toReal (P.vert m)).2 < (toReal (P.vert (m - 1))).2)
    (hbc : (toReal (P.vert m)).2 < (toReal (P.vert (m + 1))).2)
    (y : ℝ) (hlo : (toReal (P.vert m)).2 < y) (hhi : y < (toReal (P.vert m)).2 + 1)
    (hsmall : (∑ j, |(toReal (P.vert (j+1))).1 - (toReal (P.vert j)).1|)
        * (y - (toReal (P.vert m)).2) < 1/2) :
    (P.edgeThr y (m-1) < (toReal (P.vert m)).1 + 1/2 ∧
     P.edgeThr y m < (toReal (P.vert m)).1 + 1/2) ∧
    ∀ i ∈ P.spanningSet y, i ≠ m - 1 → i ≠ m →
      (toReal (P.vert m)).1 + 1/2 < P.edgeThr y i := by
  classical
  have hbound : ∀ i : ZMod P.n,
      |(toReal (P.vert (i+1))).1 - (toReal (P.vert i)).1|
        ≤ ∑ j, |(toReal (P.vert (j+1))).1 - (toReal (P.vert j)).1| :=
    fun i => Finset.single_le_sum
      (f := fun j => |(toReal (P.vert (j+1))).1 - (toReal (P.vert j)).1|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hyym : (0:ℝ) < y - (toReal (P.vert m)).2 := by linarith
  -- crossing of edge `m-1` (floor = terminal vert m) hugs xm
  have hm1 : P.edgeThr y (m-1) < (toReal (P.vert m)).1 + 1/2 := by
    have hfl := crossThreshold_near_floor_tgt (toReal (P.vert (m-1))) (toReal (P.vert m))
        (toReal (P.vert m)).2 y rfl (lex_lowest_height_gap P m (m-1) hlex (ne_of_gt hba)) hlo
    rw [show crossThreshold (toReal (P.vert (m-1))) (toReal (P.vert m)) y = P.edgeThr y (m-1) from
      by unfold LatticePolygon.edgeThr; rw [sub_add_cancel]] at hfl
    have hb : |(toReal (P.vert m)).1 - (toReal (P.vert (m-1))).1|
        ≤ ∑ j, |(toReal (P.vert (j+1))).1 - (toReal (P.vert j)).1| := by
      have := hbound (m-1); rw [sub_add_cancel] at this; exact this
    have hlt : |P.edgeThr y (m-1) - (toReal (P.vert m)).1| < 1/2 :=
      lt_of_le_of_lt hfl (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hb (le_of_lt hyym)) hsmall)
    have := (abs_lt.mp hlt).2; linarith
  -- crossing of edge `m` (floor = source vert m) hugs xm
  have hm0 : P.edgeThr y m < (toReal (P.vert m)).1 + 1/2 := by
    have hfl := crossThreshold_near_floor_src (toReal (P.vert m)) (toReal (P.vert (m+1)))
        (toReal (P.vert m)).2 y rfl (lex_lowest_height_gap P m (m+1) hlex (ne_of_gt hbc)) hlo
    rw [show crossThreshold (toReal (P.vert m)) (toReal (P.vert (m+1))) y = P.edgeThr y m from rfl] at hfl
    have hlt : |P.edgeThr y m - (toReal (P.vert m)).1| < 1/2 :=
      lt_of_le_of_lt hfl (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hbound m) (le_of_lt hyym)) hsmall)
    have := (abs_lt.mp hlt).2; linarith
  refine ⟨⟨hm1, hm0⟩, ?_⟩
  intro i hiS hi1 hi0
  rw [spanning_at_lowest_band P m hlex y hlo hhi] at hiS
  rcases hiS with ⟨hieq, hi1ne⟩ | ⟨hi1eq, hine⟩
  · -- vert i at floor (i ≠ m), vert (i+1) above
    have hgap : (toReal (P.vert m)).1 + 1 ≤ (toReal (P.vert i)).1 :=
      lex_lowest_x_gap P hS m i hlex hi0 hieq
    have hfl := crossThreshold_near_floor_src (toReal (P.vert i)) (toReal (P.vert (i+1)))
        (toReal (P.vert m)).2 y hieq (lex_lowest_height_gap P m (i+1) hlex hi1ne) hlo
    rw [show crossThreshold (toReal (P.vert i)) (toReal (P.vert (i+1))) y = P.edgeThr y i from rfl] at hfl
    have hlt : |P.edgeThr y i - (toReal (P.vert i)).1| < 1/2 :=
      lt_of_le_of_lt hfl (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hbound i) (le_of_lt hyym)) hsmall)
    have := (abs_lt.mp hlt).1; linarith
  · -- vert (i+1) at floor (i+1 ≠ m), vert i above
    have hi1m : i + 1 ≠ m := by intro h; exact hi1 (by rw [← h]; ring)
    have hgap : (toReal (P.vert m)).1 + 1 ≤ (toReal (P.vert (i+1))).1 :=
      lex_lowest_x_gap P hS m (i+1) hlex hi1m hi1eq
    have hfl := crossThreshold_near_floor_tgt (toReal (P.vert i)) (toReal (P.vert (i+1)))
        (toReal (P.vert m)).2 y hi1eq (lex_lowest_height_gap P m i hlex hine) hlo
    rw [show crossThreshold (toReal (P.vert i)) (toReal (P.vert (i+1))) y = P.edgeThr y i from rfl] at hfl
    have hlt : |P.edgeThr y i - (toReal (P.vert (i+1))).1| < 1/2 :=
      lt_of_le_of_lt hfl (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hbound i) (le_of_lt hyym)) hsmall)
    have := (abs_lt.mp hlt).1; linarith

/-- A nonzero planar cross product certifies linear independence of the two vectors. -/
lemma linearIndependent_of_cross_ne_zero (u v : ℝ × ℝ) (h : cross u v ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at hst
  obtain ⟨h1, h2⟩ := hst
  unfold cross at h
  have hs : s * (u.1 * v.2 - u.2 * v.1) = 0 := by linear_combination v.2 * h1 - v.1 * h2
  have ht : t * (u.1 * v.2 - u.2 * v.1) = 0 := by linear_combination -u.2 * h1 + u.1 * h2
  exact ⟨(mul_eq_zero.mp hs).resolve_right h, (mul_eq_zero.mp ht).resolve_right h⟩

/-- Two adjacent sides of a nondegenerate triangle meet exactly at their shared
vertex `b`: from `cross (a - b) (c - b) ≠ 0`. -/
lemma segment_adjacent_inter_of_cross_ne_zero (a b c : ℝ × ℝ)
    (h : cross (a - b) (c - b) ≠ 0) :
    segment ℝ a b ∩ segment ℝ b c = {b} := by
  rw [segment_symm ℝ a b]
  apply segment_inter_eq_endpoint_of_linearIndependent_sub
  exact linearIndependent_of_cross_ne_zero _ _ h

/-- **Two segments sharing an endpoint `c` meet only at `c`, unless the far ends
point along the same ray from `c`.** This strengthens
`segment_inter_eq_endpoint_of_linearIndependent_sub` (which needs linear
independence) to also cover the *antiparallel* collinear case `x − c`, `y − c`
opposite: the only excluded configuration is `SameRay ℝ (x − c) (y − c)` (the two
segments overlapping along a common ray). -/
lemma segment_inter_eq_endpoint_of_not_sameRay {E : Type*}
    [AddCommGroup E] [Module ℝ E] (c x y : E)
    (h : ¬ SameRay ℝ (x - c) (y - c)) :
    segment ℝ c x ∩ segment ℝ c y = {c} := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzx, hzy⟩
    by_cases hzc : z = c
    · simp [hzc]
    · exfalso; apply h
      -- z-c is same-ray with x-z and with y-z; combine to x-c, y-c
      have h1 : SameRay ℝ (z - c) (x - z) := mem_segment_iff_sameRay.mp hzx
      have h2 : SameRay ℝ (z - c) (y - z) := mem_segment_iff_sameRay.mp hzy
      have hzc' : z - c ≠ 0 := sub_ne_zero.mpr hzc
      have hx : SameRay ℝ (z - c) (x - c) := by
        have := (SameRay.rfl : SameRay ℝ (z - c) (z - c)).add_right h1
        rwa [show (z - c) + (x - z) = x - c by abel] at this
      have hy : SameRay ℝ (z - c) (y - c) := by
        have := (SameRay.rfl : SameRay ℝ (z - c) (z - c)).add_right h2
        rwa [show (z - c) + (y - z) = y - c by abel] at this
      exact (hx.symm).trans hy (fun hcontra => absurd hcontra hzc')
  · simp [Set.singleton_subset_iff, left_mem_segment]

/-- **Conjunct 4: the ear triangle is positively oriented.** Its shoelace equals
half the corner cross at the clipped vertex `m+1`, which is positive by the ear
hypothesis. -/
lemma earTri_positivelyOriented_of_isEar (R : LatticePolygon) (m : ℕ)
    (hm : R.n = m + 2) (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    (earTri R m hm).PositivelyOriented := by
  unfold LatticePolygon.PositivelyOriented
  rw [earTri_shoelace_eq_cornerCross R m hm]
  exact div_pos hear.1 (by norm_num)

/-- **Conjunct 3: the ear triangle is simple.** A triangle whose clipped corner
cross is nonzero is nondegenerate, so its three sides meet only at shared
vertices (non-adjacent sides are vacuously disjoint at `n = 3`). -/
lemma earTri_isSimple_of_cornerCross_ne (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2)
    (hne : cornerCross R ((m : ZMod R.n) + 1) ≠ 0) :
    (earTri R m hm).IsSimple := by
  -- the triangle's signed-area cross product is the clipped corner cross
  have hg : cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
      (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n))) ≠ 0 := by
    have h2 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
      have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
      push_cast at hz; linear_combination hz
    have h1 : ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) := by ring
    rw [show cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
          (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n)))
        = cornerCross R ((m : ZMod R.n) + 1) by
      unfold cornerCross; rw [h1, h2]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring]
    exact hne
  set a := toReal (R.vert (m : ZMod R.n)) with ha
  set b := toReal (R.vert ((m : ZMod R.n) + 1)) with hb
  set c := toReal (R.vert 0) with hc
  -- the three side cross products, all equal to ± hg, hence nonzero
  have hAB : cross (a - b) (c - b) ≠ 0 := fun he => hg (by
    rw [show cross (b - a) (c - a) = -cross (a - b) (c - b) by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring, he, neg_zero])
  have hBC : cross (b - c) (a - c) ≠ 0 := fun he => hg (by
    rw [show cross (b - a) (c - a) = -cross (b - c) (a - c) by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring, he, neg_zero])
  have hCA : cross (c - a) (b - a) ≠ 0 := fun he => hg (by
    rw [show cross (b - a) (c - a) = -cross (c - a) (b - a) by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring, he, neg_zero])
  refine ⟨?_, ?_, ?_⟩
  · -- no degenerate edge
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp only [earTri]
    · intro he
      exact hAB (by rw [show a = b from congrArg toReal he, sub_self]; simp [cross])
    · intro he
      exact hBC (by rw [show b = c from congrArg toReal he, sub_self]; simp [cross])
    · intro he
      exact hCA (by rw [show c = a from congrArg toReal he, sub_self]; simp [cross])
  · -- non-adjacent edges: vacuous at n = 3
    intro i j h1 h2 h3
    have key : ∀ i j : ZMod 3, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → False := by decide
    exact absurd (key i j h1 h2 h3) (by simp)
  · -- adjacent edges meet exactly at the shared vertex
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp only [LatticePolygon.edgeSeg, earTri]
    · exact segment_adjacent_inter_of_cross_ne_zero _ _ _ hAB
    · exact segment_adjacent_inter_of_cross_ne_zero _ _ _ hBC
    · exact segment_adjacent_inter_of_cross_ne_zero _ _ _ hCA

/-! ### Lattice shear (flat-bottom genericity)

A vertical **shear** `S(x,y) = (x, y + k·x)` (`k : ℤ`) is a lattice-preserving affine
bijection of `ℝ²` with determinant `1`. It preserves `cross` (hence `cornerCross` and
`shoelace`), maps edges to edges (hence preserves simplicity), and — for a generic `k`
— makes all vertex heights distinct. This breaks the flat-bottom degeneracy so the
unique-lowest convex-vertex lemma applies. -/

/-- The shear as an `ℝ`-linear equivalence `(x,y) ↦ (x, y + k·x)`. Determinant `1`,
inverse `(x,y) ↦ (x, y − k·x)`. -/
noncomputable def shearLin (k : ℝ) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1, p.2 + k * p.1)
  invFun p := (p.1, p.2 - k * p.1)
  left_inv p := by simp
  right_inv p := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ext <;> simp; ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Prod.smul_mk, smul_eq_mul]
    ext <;> simp; ring

@[simp] lemma shearLin_apply (k : ℝ) (p : ℝ × ℝ) :
    shearLin k p = (p.1, p.2 + k * p.1) := rfl

/-- The sheared lattice polygon: each lattice vertex `(x,y)` becomes `(x, y + k·x)`,
which is again a lattice point (`k : ℤ`). -/
def shearP (P : LatticePolygon) (k : ℤ) : LatticePolygon where
  n := P.n
  pos := P.pos
  vert i := ((P.vert i).1, (P.vert i).2 + k * (P.vert i).1)

@[simp] lemma shearP_n (P : LatticePolygon) (k : ℤ) : (shearP P k).n = P.n := rfl

@[simp] lemma shearP_vert (P : LatticePolygon) (k : ℤ) (i : ZMod P.n) :
    (shearP P k).vert i = ((P.vert i).1, (P.vert i).2 + k * (P.vert i).1) := rfl

/-- The real coordinates of a sheared vertex are the shear-map image of the originals. -/
lemma shearP_toReal (P : LatticePolygon) (k : ℤ) (i : ZMod P.n) :
    toReal ((shearP P k).vert i) = shearLin (k : ℝ) (toReal (P.vert i)) := by
  simp only [shearP_vert, toReal, shearLin_apply]
  push_cast
  ring_nf

/-- `cross` is invariant under the shear (the shear matrix has determinant `1`). -/
lemma cross_shearLin (k : ℝ) (u v : ℝ × ℝ) :
    cross (shearLin k u) (shearLin k v) = cross u v := by
  simp only [shearLin_apply, cross]; ring

/-- The shear preserves the corner cross at every vertex. -/
lemma shearP_cornerCross (P : LatticePolygon) (k : ℤ) (i : ZMod P.n) :
    cornerCross (shearP P k) i = cornerCross P i := by
  unfold cornerCross
  rw [shearP_toReal, shearP_toReal, shearP_toReal, ← map_sub, ← map_sub]
  exact cross_shearLin _ _ _

/-- The shear preserves the shoelace (signed) area. -/
lemma shearP_shoelace (P : LatticePolygon) (k : ℤ) :
    (shearP P k).shoelace = P.shoelace := by
  unfold LatticePolygon.shoelace
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [shearP_toReal, shearP_toReal]
  exact cross_shearLin _ _ _

/-- The shear preserves positive orientation (via the shoelace). -/
lemma shearP_positivelyOriented (P : LatticePolygon) (k : ℤ)
    (hO : P.PositivelyOriented) : (shearP P k).PositivelyOriented := by
  unfold LatticePolygon.PositivelyOriented at *
  rw [shearP_shoelace]; exact hO

/-- Sheared edges are the shear-image of the original edges. -/
lemma shearP_edgeSeg (P : LatticePolygon) (k : ℤ) (i : ZMod P.n) :
    (shearP P k).edgeSeg i
      = (shearLin (k:ℝ)) '' (P.edgeSeg (i : ZMod P.n)) := by
  simp only [LatticePolygon.edgeSeg, shearP_toReal]
  have := image_segment ℝ (shearLin (k:ℝ)).toLinearMap.toAffineMap
    (toReal (P.vert i)) (toReal (P.vert (i + 1)))
  simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] at this ⊢
  exact this.symm

/-- The shear preserves simplicity (it is an injective affine map sending edges to
edges). -/
lemma shearP_isSimple (P : LatticePolygon) (k : ℤ) (hS : P.IsSimple) :
    (shearP P k).IsSimple := by
  obtain ⟨hdeg, hdisj, hadj⟩ := hS
  have hinj : Function.Injective (shearLin (k:ℝ)) := (shearLin (k:ℝ)).injective
  -- forget that the index lives in `ZMod (shearP P k).n`; it *is* `ZMod P.n`.
  show (⟨P.n, P.pos, fun i => ((P.vert i).1, (P.vert i).2 + k * (P.vert i).1)⟩
      : LatticePolygon).IsSimple
  have hedge : ∀ i : ZMod P.n,
      (⟨P.n, P.pos, fun i => ((P.vert i).1, (P.vert i).2 + k * (P.vert i).1)⟩
        : LatticePolygon).edgeSeg i = (shearLin (k:ℝ)) '' (P.edgeSeg i) :=
    fun i => shearP_edgeSeg P k i
  have hvert : ∀ i : ZMod P.n,
      toReal ((⟨P.n, P.pos, fun i => ((P.vert i).1, (P.vert i).2 + k * (P.vert i).1)⟩
        : LatticePolygon).vert i) = shearLin (k:ℝ) (toReal (P.vert i)) :=
    fun i => shearP_toReal P k i
  refine ⟨?_, ?_, ?_⟩
  · -- no degenerate edge
    intro i he
    apply hdeg i
    apply toReal_injective
    apply hinj
    have he' := congrArg toReal he
    rw [hvert, hvert] at he'; exact he'
  · -- non-adjacent disjoint
    intro i j hij hi1j hj1i
    rw [hedge, hedge]
    exact Set.disjoint_image_of_injective hinj (hdisj i j hij hi1j hj1i)
  · -- adjacent meet exactly at shared vertex
    intro i
    rw [hedge, hedge, ← Set.image_inter hinj, hadj i, Set.image_singleton, hvert]

/-- **Generic shear coefficient.** For a simple polygon there is an integer `k` whose
shear separates all vertex heights: `(P.vert i).2 + k·(P.vert i).1` are pairwise
distinct. The bad `k` for a pair with distinct `x` is a single value bounded by the
height gap; pairs with equal `x` never tie (distinct vertices ⟹ distinct `y`). Taking
`k` larger than every height gap avoids all of them. -/
lemma exists_generic_shear (P : LatticePolygon) (hS : P.IsSimple) :
    ∃ k : ℤ, ∀ i j : ZMod P.n, i ≠ j →
      (P.vert i).2 + k * (P.vert i).1 ≠ (P.vert j).2 + k * (P.vert j).1 := by
  classical
  let g : ZMod P.n × ZMod P.n → ℤ := fun p => |(P.vert p.1).2 - (P.vert p.2).2|
  let B : ℤ := ∑ p ∈ (Finset.univ : Finset (ZMod P.n × ZMod P.n)), g p
  refine ⟨B + 1, fun i j hij htie => ?_⟩
  -- distinct indices ⟹ distinct vertices
  have hvne : P.vert i ≠ P.vert j := fun h => hij (vert_injective P hS h)
  -- rearrange the tie: (B+1)·(xi − xj) = yj − yi
  have hrear : (B + 1) * ((P.vert i).1 - (P.vert j).1)
      = (P.vert j).2 - (P.vert i).2 := by linear_combination htie
  -- bound: |yj − yi| ≤ B  (it is the (j,i) summand of a sum of nonneg terms)
  have hbound : |(P.vert j).2 - (P.vert i).2| ≤ B :=
    Finset.single_le_sum (f := g) (fun p _ => abs_nonneg _) (Finset.mem_univ (j, i))
  by_cases hx : (P.vert i).1 = (P.vert j).1
  · -- equal x ⟹ equal y (from the tie) ⟹ vertices equal, contradiction
    rw [hx, sub_self, mul_zero] at hrear
    have hy : (P.vert i).2 = (P.vert j).2 := by linarith
    exact hvne (Prod.ext hx hy)
  · -- distinct x: |B+1|·|Δx| ≤ B but |B+1| ≥ B+1 and |Δx| ≥ 1, contradiction
    have hdx : (1 : ℤ) ≤ |(P.vert i).1 - (P.vert j).1| :=
      Int.one_le_abs (sub_ne_zero.mpr hx)
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun p _ => abs_nonneg _)
    have habs : |(B + 1) * ((P.vert i).1 - (P.vert j).1)|
        = |(P.vert j).2 - (P.vert i).2| := by rw [hrear]
    rw [abs_mul] at habs
    have hB1 : |B + 1| = B + 1 := abs_of_pos (by omega)
    rw [hB1] at habs
    -- (B+1)·|Δx| = |Δy| ≤ B, but (B+1)·|Δx| ≥ B+1 > B
    have hge : B + 1 ≤ (B + 1) * |(P.vert i).1 - (P.vert j).1| := by
      have := mul_le_mul_of_nonneg_left hdx (by omega : (0:ℤ) ≤ B + 1)
      linarith [this]
    rw [habs] at hge
    linarith [hbound]

/-! ### General lattice linear map (exposing extreme vertices in any rational direction)

For integers `c, d` not both zero, the linear map `L(x,y) = (d·x − c·y, c·x + d·y)` has
determinant `c² + d² > 0`, so it preserves `cross` up to the positive factor `c² + d²`
(hence the sign of `cornerCross` and of the shoelace), is injective, and maps edges to
edges (preserving simplicity).  Crucially, the *height* (second coordinate) of the
transformed vertex is the linear functional `c·x + d·y`; minimising it over the vertices
selects the vertex extreme in the direction `(c, d)`, which is therefore convex.  This is
what `shearP` does only for the directions `(k, 1)`; the general map reaches every rational
direction, exposing enough convex vertices to dodge any two prescribed indices. -/

/-- The `ℝ`-linear map `(x,y) ↦ (d·x − c·y, c·x + d·y)` (determinant `c² + d²`). -/
def linLinMap (c d : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (d * p.1 - c * p.2, c * p.1 + d * p.2)
  map_add' a b := by ext <;> simp <;> ring
  map_smul' r p := by ext <;> simp <;> ring

@[simp] lemma linLinMap_apply (c d : ℝ) (p : ℝ × ℝ) :
    linLinMap c d p = (d * p.1 - c * p.2, c * p.1 + d * p.2) := rfl

/-- `cross` scales by the determinant `c² + d²` under `linLinMap`. -/
lemma cross_linLinMap (c d : ℝ) (u v : ℝ × ℝ) :
    cross (linLinMap c d u) (linLinMap c d v) = (c ^ 2 + d ^ 2) * cross u v := by
  simp only [linLinMap_apply, cross]; ring

/-- `linLinMap c d` is injective when `c² + d² ≠ 0` (i.e. `(c,d) ≠ 0`). -/
lemma linLinMap_injective (c d : ℝ) (h : c ^ 2 + d ^ 2 ≠ 0) :
    Function.Injective (linLinMap c d) := by
  intro u v huv
  have h1 : d * u.1 - c * u.2 = d * v.1 - c * v.2 := congrArg Prod.fst huv
  have h2 : c * u.1 + d * u.2 = c * v.1 + d * v.2 := congrArg Prod.snd huv
  have hx : (c ^ 2 + d ^ 2) * (u.1 - v.1) = 0 := by linear_combination c * h2 + d * h1
  have hy : (c ^ 2 + d ^ 2) * (u.2 - v.2) = 0 := by linear_combination d * h2 - c * h1
  have e1 : u.1 = v.1 := sub_eq_zero.mp ((mul_eq_zero.1 hx).resolve_left h)
  have e2 : u.2 = v.2 := sub_eq_zero.mp ((mul_eq_zero.1 hy).resolve_left h)
  exact Prod.ext e1 e2

/-- The general lattice linear image: each vertex `(x,y)` becomes
`(d·x − c·y, c·x + d·y)`, again a lattice point (`c, d : ℤ`). -/
def linP (P : LatticePolygon) (c d : ℤ) : LatticePolygon where
  n := P.n
  pos := P.pos
  vert i := (d * (P.vert i).1 - c * (P.vert i).2, c * (P.vert i).1 + d * (P.vert i).2)

@[simp] lemma linP_n (P : LatticePolygon) (c d : ℤ) : (linP P c d).n = P.n := rfl

@[simp] lemma linP_vert (P : LatticePolygon) (c d : ℤ) (i : ZMod P.n) :
    (linP P c d).vert i =
      (d * (P.vert i).1 - c * (P.vert i).2, c * (P.vert i).1 + d * (P.vert i).2) := rfl

/-- The real coordinates of a transformed vertex are the `linLinMap` image. -/
lemma linP_toReal (P : LatticePolygon) (c d : ℤ) (i : ZMod P.n) :
    toReal ((linP P c d).vert i) = linLinMap (c : ℝ) (d : ℝ) (toReal (P.vert i)) := by
  simp only [linP_vert, toReal, linLinMap_apply]
  push_cast; constructor

/-- The height (second real coordinate) of a transformed vertex is the functional
`c·x + d·y`. -/
lemma linP_height (P : LatticePolygon) (c d : ℤ) (i : ZMod P.n) :
    (toReal ((linP P c d).vert i)).2 = (c : ℝ) * (P.vert i).1 + (d : ℝ) * (P.vert i).2 := by
  rw [linP_toReal]; simp only [linLinMap_apply, toReal]

/-- `linP` scales `cornerCross` by the positive factor `c² + d²` (sign-preserving). -/
lemma linP_cornerCross (P : LatticePolygon) (c d : ℤ) (i : ZMod P.n) :
    cornerCross (linP P c d) i = ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) * cornerCross P i := by
  unfold cornerCross
  rw [linP_toReal, linP_toReal, linP_toReal, ← map_sub, ← map_sub]
  exact cross_linLinMap _ _ _ _

/-- `linP` scales the shoelace by `c² + d²`. -/
lemma linP_shoelace (P : LatticePolygon) (c d : ℤ) :
    (linP P c d).shoelace = ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) * P.shoelace := by
  unfold LatticePolygon.shoelace
  have hsum : (∑ i, cross (toReal ((linP P c d).vert i)) (toReal ((linP P c d).vert (i + 1))))
      = ((c : ℝ) ^ 2 + (d : ℝ) ^ 2)
        * ∑ i, cross (toReal (P.vert i)) (toReal (P.vert (i + 1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [linP_toReal, linP_toReal]
    exact cross_linLinMap _ _ _ _
  rw [hsum]; ring

/-- `linP` preserves positive orientation when `0 < c² + d²` (i.e. `(c,d) ≠ 0`). -/
lemma linP_positivelyOriented (P : LatticePolygon) (c d : ℤ)
    (hcd : (0 : ℝ) < (c : ℝ) ^ 2 + (d : ℝ) ^ 2) (hO : P.PositivelyOriented) :
    (linP P c d).PositivelyOriented := by
  unfold LatticePolygon.PositivelyOriented at *
  rw [linP_shoelace]; positivity

/-- Transformed edges are the `linLinMap` image of the original edges. -/
lemma linP_edgeSeg (P : LatticePolygon) (c d : ℤ) (i : ZMod P.n) :
    (linP P c d).edgeSeg i = (linLinMap (c : ℝ) (d : ℝ)) '' (P.edgeSeg i) := by
  simp only [LatticePolygon.edgeSeg, linP_toReal]
  have := image_segment ℝ (linLinMap (c : ℝ) (d : ℝ)).toAffineMap
    (toReal (P.vert i)) (toReal (P.vert (i + 1)))
  simp only [LinearMap.coe_toAffineMap] at this ⊢
  exact this.symm

/-- `linP` preserves simplicity when `c² + d² ≠ 0` (an injective affine image of edges). -/
lemma linP_isSimple (P : LatticePolygon) (c d : ℤ)
    (h : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 ≠ 0) (hS : P.IsSimple) : (linP P c d).IsSimple := by
  obtain ⟨hdeg, hdisj, hadj⟩ := hS
  have hinj : Function.Injective (linLinMap (c : ℝ) (d : ℝ)) := linLinMap_injective _ _ h
  show (⟨P.n, P.pos, fun i => ((d : ℤ) * (P.vert i).1 - c * (P.vert i).2,
        c * (P.vert i).1 + d * (P.vert i).2)⟩ : LatticePolygon).IsSimple
  have hedge : ∀ i : ZMod P.n,
      (⟨P.n, P.pos, fun i => ((d : ℤ) * (P.vert i).1 - c * (P.vert i).2,
        c * (P.vert i).1 + d * (P.vert i).2)⟩ : LatticePolygon).edgeSeg i
        = (linLinMap (c : ℝ) (d : ℝ)) '' (P.edgeSeg i) :=
    fun i => linP_edgeSeg P c d i
  have hvert : ∀ i : ZMod P.n,
      toReal ((⟨P.n, P.pos, fun i => ((d : ℤ) * (P.vert i).1 - c * (P.vert i).2,
        c * (P.vert i).1 + d * (P.vert i).2)⟩ : LatticePolygon).vert i)
        = linLinMap (c : ℝ) (d : ℝ) (toReal (P.vert i)) :=
    fun i => linP_toReal P c d i
  refine ⟨?_, ?_, ?_⟩
  · intro i he
    apply hdeg i
    apply toReal_injective
    apply hinj
    have he' := congrArg toReal he
    rw [hvert, hvert] at he'; exact he'
  · intro i j hij hi1j hj1i
    rw [hedge, hedge]
    exact Set.disjoint_image_of_injective hinj (hdisj i j hij hi1j hj1i)
  · intro i
    rw [hedge, hedge, ← Set.image_inter hinj, hadj i, Set.image_singleton, hvert]

/-! ### Rotation equivariance of `cornerCross`, `inTriangle`, `isEarVertex`

`rotateP P c` reindexes vertices by `i ↦ i + c`. The corner cross, the in-triangle
test, and hence the ear predicate transport accordingly: `isEarVertex (rotateP P c) i ↔
isEarVertex P (i + c)`. This lets an ear at any vertex be rotated to the last index. -/

/-- The corner cross of a rotated polygon at `i` is the original corner cross at
`i + c`. -/
lemma rotateP_cornerCross (P : LatticePolygon) (c i : ZMod P.n) :
    cornerCross (rotateP P c) i = cornerCross P (i + c) := by
  -- Retype the rotated corner cross into its unfolded `P`-indexed form (valid by
  -- defeq, since `(rotateP P c).n = P.n` and `(rotateP P c).vert x = P.vert (x + c)`),
  -- then reindex `(i ± 1) + c = i + c ± 1` and fold back into `cornerCross P (i + c)`.
  show cross (toReal (P.vert (i + c)) - toReal (P.vert ((i - 1) + c)))
        (toReal (P.vert ((i + 1) + c)) - toReal (P.vert (i + c)))
      = cornerCross P (i + c)
  rw [show (i - 1) + c = i + c - 1 from by ring, show (i + 1) + c = i + c + 1 from by ring]
  rfl

/-- **Rotation equivariance of the ear predicate.** `i` is an ear vertex of
`rotateP P c` iff `i + c` is an ear vertex of `P`. (Both the convex corner cross and
the empty-triangle test only depend on the three real vertices `vᵢ₋₁, vᵢ, vᵢ₊₁` and
the other vertices, which the rotation merely reindexes bijectively.) -/
lemma isEarVertex_rotateP (P : LatticePolygon) (c i : ZMod P.n) :
    isEarVertex (rotateP P c) i ↔ isEarVertex P (i + c) := by
  rw [isEarVertex, isEarVertex, rotateP_cornerCross]
  simp only [rotateP_vert]
  refine and_congr_right (fun _ => ?_)
  -- Retype the rotated side's binder `ZMod (rotateP P c).n` to `ZMod P.n` (defeq),
  -- keeping the apex in its `i ± 1 + c` form; now every index lives in the single ring
  -- `ZMod P.n`, so the bijective reindexing `j ↦ j ± c` is closed by `ring`.
  show (∀ (j : ZMod P.n), j ≠ i - 1 → j ≠ i → j ≠ i + 1 →
      ¬ inTriangle (toReal (P.vert (i - 1 + c))) (toReal (P.vert (i + c)))
        (toReal (P.vert (i + 1 + c))) (toReal (P.vert (j + c)))) ↔ _
  constructor
  · -- forward: a vertex `j` of `P` corresponds to `j - c` of the rotation
    intro h j hjm1 hjm hjp1
    have hj := h (j - c)
      (fun hc => hjm1 (by rw [show j = (j - c) + c by ring, hc]; ring))
      (fun hc => hjm (by rw [show j = (j - c) + c by ring, hc]))
      (fun hc => hjp1 (by rw [show j = (j - c) + c by ring, hc]; ring))
    convert hj using 4 <;> ring
  · -- backward: a rotated vertex index `j` corresponds to `j + c` of `P`
    intro h j hjm1 hjm hjp1
    have hj := h (j + c)
      (fun hc => hjm1 (add_right_cancel (b := c) (by rw [hc]; ring)))
      (fun hc => hjm (add_right_cancel (b := c) hc))
      (fun hc => hjp1 (add_right_cancel (b := c) (by rw [hc]; ring)))
    convert hj using 4 <;> ring

/-- **Ear packaging (empty-triangle ⟹ ear).** A convex vertex (`0 < cornerCross`)
whose closed corner triangle contains no other polygon vertex is an ear. This is the
trivial half of Meisters' two-ears theorem — exactly the `isEarVertex` definition — and
isolates the genuine remaining content (existence of such an empty convex triangle). -/
lemma isEarVertex_of_empty (P : LatticePolygon) (m : ZMod P.n)
    (hconv : 0 < cornerCross P m)
    (hempty : ∀ j, j ≠ m - 1 → j ≠ m → j ≠ m + 1 →
      ¬ inTriangle (toReal (P.vert (m - 1))) (toReal (P.vert m))
        (toReal (P.vert (m + 1))) (toReal (P.vert j))) :
    isEarVertex P m := ⟨hconv, hempty⟩

end Pick
