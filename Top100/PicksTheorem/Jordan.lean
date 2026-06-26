import Top100.PicksTheorem.Winding

/-!
# Polygonal Jordan curve theorem: `winding ∈ {0,1}` (in progress)

The keystone for the geometric Pick's theorem. For a **simple, positively
oriented** lattice polygon and a point `q` off the boundary, the winding number
is `0` (exterior) or `1` (interior).

## Roadmap (crossing-alternation route, reusing the local ray-casting theory)

The integer `winding q = ∑ᵢ edgeWind …` is the signed count of edges whose
rightward horizontal ray from `q` they cross. Local theory (done in `Winding`):
the winding is constant except across crossings, where it jumps by `∓1`
(`edgeWind_hshift_cross_up/_down`, `winding_hshift_eq`).

Remaining global steps (each a sub-development):
1. `winding_le_spanning` — `|winding q|` is bounded by the number of edges
   spanning `q`'s height. **(this file, done below for the crude `≤ n` bound)**
2. Crossing structure: order the crossing edges of the ray by their crossing
   `x`-coordinate (compared by cross-multiplication, no division).
3. Alternation: consecutive crossings have opposite `edgeWind` sign — uses
   `IsSimple` (edges meet only at shared vertices ⟹ the boundary is a single
   loop ⟹ the curve can't return to one side of the ray without crossing).
4. Conclude `winding ∈ {0,1}` from far-field `0` + alternating `∓1` jumps.

Then: Green (`area = shoelace`) and Hopf (boundary count `B/2 − 1`).
-/

namespace Pick

open LatticePolygon

/-- Crude global bound: `|winding q| ≤ n` (the number of edges), since each of the
`n` per-edge contributions lies in `{−1, 0, 1}`. First step toward squeezing the
winding to `{0,1}` using simplicity. -/
theorem abs_winding_le (P : LatticePolygon) (q : ℝ × ℝ) : |P.winding q| ≤ (P.n : ℤ) := by
  unfold LatticePolygon.winding
  have hb : ∀ i ∈ (Finset.univ : Finset (ZMod P.n)),
      |edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q| ≤ 1 := by
    intro i _
    rcases edgeWind_mem (toReal (P.vert i)) (toReal (P.vert (i + 1))) q with h | h | h <;>
      rw [h] <;> decide
  calc |∑ i, edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q|
      ≤ ∑ i, |edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ZMod P.n, (1 : ℤ) := Finset.sum_le_sum hb
    _ = (P.n : ℤ) := by simp [ZMod.card]

/-- The winding number is the number of **up-edges** the rightward ray crosses
minus the number of **down-edges** it crosses. The alternation argument (step 3)
shows these two counts differ by at most one, squeezing the winding to `{−1,0,1}`. -/
theorem winding_eq_card_sub (P : LatticePolygon) (q : ℝ × ℝ) :
    P.winding q =
      ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q = 1).card : ℤ)
      - (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q = -1).card := by
  classical
  unfold LatticePolygon.winding
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases edgeWind_mem (toReal (P.vert i)) (toReal (P.vert (i + 1))) q with h | h | h <;>
    rw [h] <;> norm_num

/-- At any height `y`, the number of edges crossing it **upward** equals the
number crossing it **downward** — the boundary is a closed loop, so its
`y`-coordinate returns to its start (this telescopes; no simplicity needed). -/
theorem card_up_eq_card_down (P : LatticePolygon) (y : ℝ) :
    (Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card =
    (Finset.univ.filter fun i =>
        (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2).card := by
  classical
  have key :
      (((Finset.univ.filter fun i =>
          (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card : ℤ)) -
      ((Finset.univ.filter fun i =>
          (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2).card) = 0 := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_sub_distrib]
    have per : ∀ i,
        ((if (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else 0) -
          if (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2 then 1 else 0) =
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else 0) -
          (if y < (toReal (P.vert i)).2 then 1 else 0) := by
      intro i
      by_cases hai : (toReal (P.vert i)).2 ≤ y <;> by_cases hbi : (toReal (P.vert (i + 1))).2 ≤ y
      · rw [if_neg fun h => absurd h.2 (not_lt.mpr hbi), if_neg fun h => absurd h.2 (not_lt.mpr hai),
          if_neg (not_lt.mpr hbi), if_neg (not_lt.mpr hai)]
      · rw [if_pos ⟨hai, not_le.mp hbi⟩, if_neg fun h => absurd h.1 hbi,
          if_pos (not_le.mp hbi), if_neg (not_lt.mpr hai)]
      · rw [if_neg fun h => absurd h.1 hai, if_pos ⟨hbi, not_le.mp hai⟩,
          if_neg (not_lt.mpr hbi), if_pos (not_le.mp hai)]
      · rw [if_neg fun h => absurd h.1 hai, if_neg fun h => absurd h.1 hbi,
          if_pos (not_le.mp hbi), if_pos (not_le.mp hai)]
        norm_num
    rw [Finset.sum_congr rfl fun i _ => per i, Finset.sum_sub_distrib]
    have reindex :
        (∑ i, if y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else 0) =
          ∑ i, if y < (toReal (P.vert i)).2 then (1 : ℤ) else 0 :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n))
        (fun i => if y < (toReal (P.vert i)).2 then (1 : ℤ) else 0)
    rw [reindex, sub_self]
  omega

/-- For an **up-edge** at a fixed height `y`, the contribution `edgeWind` is
antitone in `x`: the "already-crossed" region (`edgeWind = 1`, i.e. `q` left of
the edge) is a left-ray `x < x*`. So the rightward ray crosses each edge at a
single `x`-threshold — the basis for ordering the crossings. -/
lemma edgeWind_up_antitone (a b : ℝ × ℝ) (y x1 x2 : ℝ) (hx : x1 ≤ x2)
    (h1 : a.2 ≤ y) (h2 : y < b.2) :
    edgeWind a b (x2, y) ≤ edgeWind a b (x1, y) := by
  have key : ∀ x : ℝ, edgeWind a b (x, y) ≠ -1 := by
    intro x h
    have hlt : y < a.2 := (edgeWind_eq_neg_one_imp a b (x, y) h).2
    linarith
  have imp : edgeWind a b (x2, y) = 1 → edgeWind a b (x1, y) = 1 := by
    intro h
    have hc2 : 0 < cross (b - a) ((x2, y) - a) := ((edgeWind_eq_one_iff a b (x2, y)).mp h).2.2
    have hdiff : cross (b - a) ((x1, y) - a) - cross (b - a) ((x2, y) - a)
        = (b.2 - a.2) * (x2 - x1) := by
      unfold cross; simp only [Prod.fst_sub, Prod.snd_sub]; ring
    have hc1 : 0 < cross (b - a) ((x1, y) - a) := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ b.2 - a.2 by linarith)
        (show (0:ℝ) ≤ x2 - x1 by linarith)]
    exact (edgeWind_eq_one_iff a b (x1, y)).mpr ⟨h1, h2, hc1⟩
  rcases edgeWind_mem a b (x1, y) with a1 | a1 | a1
  · exact absurd a1 (key x1)
  · rcases edgeWind_mem a b (x2, y) with a2 | a2 | a2
    · exact absurd a2 (key x2)
    · rw [a1, a2]
    · have h := imp a2; rw [a1] at h; norm_num at h
  · rcases edgeWind_mem a b (x2, y) with a2 | a2 | a2
    · exact absurd a2 (key x2)
    · rw [a1, a2]; norm_num
    · rw [a1, a2]

/-- For a **down-edge** at fixed height `y`, `edgeWind` is monotone in `x`: the
crossed region (`edgeWind = −1`) is a left-ray `x < x*`. Companion to
`edgeWind_up_antitone`; together they give the single-`x`-threshold crossing
property for every edge orientation. -/
lemma edgeWind_down_monotone (a b : ℝ × ℝ) (y x1 x2 : ℝ) (hx : x1 ≤ x2)
    (h1 : b.2 ≤ y) (h2 : y < a.2) :
    edgeWind a b (x1, y) ≤ edgeWind a b (x2, y) := by
  have key : ∀ x : ℝ, edgeWind a b (x, y) ≠ 1 := by
    intro x h
    have hlt : y < b.2 := (edgeWind_eq_one_imp a b (x, y) h).2
    linarith
  have imp : edgeWind a b (x2, y) = -1 → edgeWind a b (x1, y) = -1 := by
    intro h
    have hc2 : cross (b - a) ((x2, y) - a) < 0 := ((edgeWind_eq_neg_one_iff a b (x2, y)).mp h).2.2
    have hdiff : cross (b - a) ((x2, y) - a) - cross (b - a) ((x1, y) - a)
        = (a.2 - b.2) * (x2 - x1) := by
      unfold cross; simp only [Prod.fst_sub, Prod.snd_sub]; ring
    have hc1 : cross (b - a) ((x1, y) - a) < 0 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ a.2 - b.2 by linarith)
        (show (0:ℝ) ≤ x2 - x1 by linarith)]
    exact (edgeWind_eq_neg_one_iff a b (x1, y)).mpr ⟨h1, h2, hc1⟩
  rcases edgeWind_mem a b (x1, y) with a1 | a1 | a1
  · rcases edgeWind_mem a b (x2, y) with a2 | a2 | a2
    · rw [a1, a2]
    · rw [a1, a2]; norm_num
    · exact absurd a2 (key x2)
  · rcases edgeWind_mem a b (x2, y) with a2 | a2 | a2
    · have h := imp a2; rw [a1] at h; norm_num at h
    · rw [a1, a2]
    · exact absurd a2 (key x2)
  · exact absurd a1 (key x1)

/-- The number of edges crossing any height `y` is **even**: up- and down-
crossings are disjoint and equinumerous (`card_up_eq_card_down`), so the total is
`2 · #up`. This is the parity precursor to the Jordan crossing argument. -/
theorem card_spanning_even (P : LatticePolygon) (y : ℝ) :
    Even (Finset.univ.filter fun i =>
      ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card := by
  classical
  have hdisj : Disjoint
      (Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2)
      (Finset.univ.filter fun i =>
        (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2) := by
    rw [Finset.disjoint_filter]
    rintro i _ ⟨_, hub⟩ ⟨hdb, _⟩
    linarith
  rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj, card_up_eq_card_down]
  exact ⟨_, rfl⟩

/-- The `x`-coordinate where the (non-horizontal) edge `a → b` crosses height
`y`. The rightward ray from `(x, y)` crosses the edge iff `x < crossThreshold`. -/
noncomputable def crossThreshold (a b : ℝ × ℝ) (y : ℝ) : ℝ :=
  a.1 + (b.1 - a.1) * (y - a.2) / (b.2 - a.2)

/-- The threshold point `(x*, y)` lies on the edge's line: `cross = 0` there.
This pins down `crossThreshold` as the sign-change locus of `cross`, the basis
for comparing crossings by `x`. -/
lemma cross_crossThreshold (a b : ℝ × ℝ) (y : ℝ) (hne : b.2 ≠ a.2) :
    cross (b - a) ((crossThreshold a b y, y) - a) = 0 := by
  have hd : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr hne
  unfold cross crossThreshold
  simp only [Prod.fst_sub, Prod.snd_sub]
  field_simp
  ring

/-- For an up-edge (`a.2 < b.2`), the ray-crossing condition `cross > 0`
(equivalently `edgeWind = 1` within the `y`-range) is exactly `x < x*`. So the
crossing happens precisely at the threshold `x*`. -/
lemma cross_pos_iff_lt_threshold (a b : ℝ × ℝ) (y x : ℝ) (hlt : a.2 < b.2) :
    0 < cross (b - a) ((x, y) - a) ↔ x < crossThreshold a b y := by
  have hd : (0:ℝ) < b.2 - a.2 := by linarith
  unfold cross crossThreshold
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [← sub_lt_iff_lt_add', lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- For a down-edge (`b.2 < a.2`), the ray-crossing condition `cross < 0`
(equivalently `edgeWind = −1` within the `y`-range) is exactly `x < x*`. -/
lemma cross_neg_iff_lt_threshold (a b : ℝ × ℝ) (y x : ℝ) (hlt : b.2 < a.2) :
    cross (b - a) ((x, y) - a) < 0 ↔ x < crossThreshold a b y := by
  have hd : (b.2 - a.2) < 0 := by linarith
  unfold cross crossThreshold
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [← sub_lt_iff_lt_add', lt_div_iff_of_neg hd]
  constructor <;> intro h <;> nlinarith

/-- The crossing `x` is independent of edge orientation: `a → b` and `b → a` give
the same threshold (it's where the common line meets height `y`). -/
lemma crossThreshold_comm (a b : ℝ × ℝ) (y : ℝ) (hne : a.2 ≠ b.2) :
    crossThreshold a b y = crossThreshold b a y := by
  have h1 : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2 : a.2 - b.2 ≠ 0 := sub_ne_zero.mpr hne
  unfold crossThreshold
  field_simp
  ring

/-- The threshold point lies on the edge **segment** (not just its line) when `y`
is strictly between the endpoint heights: it is `(1−t)·a + t·b` with
`t = (y−a.2)/(b.2−a.2) ∈ (0,1)`. The geometric input for distinctness of
crossings on disjoint edges. -/
lemma crossThreshold_mem_segment (a b : ℝ × ℝ) (y : ℝ) (h1 : a.2 < y) (h2 : y < b.2) :
    (crossThreshold a b y, y) ∈ segment ℝ a b := by
  have hd : (0:ℝ) < b.2 - a.2 := by linarith
  rw [segment_eq_image]
  refine ⟨(y - a.2) / (b.2 - a.2), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one hd]; linarith
  · have hne : b.2 - a.2 ≠ 0 := ne_of_gt hd
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, crossThreshold]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      ring

/-- Down-orientation companion: the threshold point is on the segment when the
edge descends through `y` (`b.2 < y < a.2`). -/
lemma crossThreshold_mem_segment_down (a b : ℝ × ℝ) (y : ℝ) (h1 : b.2 < y) (h2 : y < a.2) :
    (crossThreshold a b y, y) ∈ segment ℝ a b := by
  rw [crossThreshold_comm a b y (by linarith : a.2 ≠ b.2), segment_symm]
  exact crossThreshold_mem_segment b a y h1 h2

/-- **First use of `IsSimple`.** Two non-adjacent edges that both cross height `y`
(strictly, upward) have distinct crossing `x`-coordinates: equal thresholds would
put the shared crossing point on both disjoint edge segments. So the rightward
ray meets distinct edges at distinct points — the crossings are strictly ordered
by `x`. -/
lemma crossThreshold_ne_of_simple (P : LatticePolygon) (hP : P.IsSimple) (y : ℝ)
    (i j : ZMod P.n) (hij : i ≠ j) (h1 : i + 1 ≠ j) (h2 : j + 1 ≠ i)
    (hi1 : (toReal (P.vert i)).2 < y) (hi2 : y < (toReal (P.vert (i + 1))).2)
    (hj1 : (toReal (P.vert j)).2 < y) (hj2 : y < (toReal (P.vert (j + 1))).2) :
    crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y
      ≠ crossThreshold (toReal (P.vert j)) (toReal (P.vert (j + 1))) y := by
  intro heq
  have memi : (crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y, y)
      ∈ P.edgeSeg i := crossThreshold_mem_segment _ _ y hi1 hi2
  have memj : (crossThreshold (toReal (P.vert j)) (toReal (P.vert (j + 1))) y, y)
      ∈ P.edgeSeg j := crossThreshold_mem_segment _ _ y hj1 hj2
  rw [heq] at memi
  exact Set.disjoint_left.mp (hP.2.1 i j hij h1 h2) memi memj

/-- Clean indicator form of `edgeWind` for a strictly-spanning **up-edge**:
`edgeWind = 1` exactly left of the threshold, `0` to its right. This is the form
the sorted-threshold/alternation argument manipulates. -/
lemma edgeWind_eq_indicator_up (a b : ℝ × ℝ) (y x : ℝ) (h1 : a.2 < y) (h2 : y < b.2) :
    edgeWind a b (x, y) = if x < crossThreshold a b y then 1 else 0 := by
  by_cases hx : x < crossThreshold a b y
  · rw [if_pos hx]
    exact (edgeWind_eq_one_iff a b (x, y)).mpr
      ⟨le_of_lt h1, h2, (cross_pos_iff_lt_threshold a b y x (by linarith)).mpr hx⟩
  · rw [if_neg hx]
    rcases edgeWind_mem a b (x, y) with h | h | h
    · exfalso
      have hh : y < a.2 := (edgeWind_eq_neg_one_imp a b (x, y) h).2
      linarith
    · exact h
    · exfalso
      have hc : 0 < cross (b - a) ((x, y) - a) := ((edgeWind_eq_one_iff a b (x, y)).mp h).2.2
      exact hx ((cross_pos_iff_lt_threshold a b y x (by linarith)).mp hc)

/-- Indicator form of `edgeWind` for a strictly-spanning **down-edge**:
`edgeWind = −1` left of the threshold, `0` to its right. -/
lemma edgeWind_eq_indicator_down (a b : ℝ × ℝ) (y x : ℝ) (h1 : b.2 < y) (h2 : y < a.2) :
    edgeWind a b (x, y) = if x < crossThreshold a b y then -1 else 0 := by
  by_cases hx : x < crossThreshold a b y
  · rw [if_pos hx]
    exact (edgeWind_eq_neg_one_iff a b (x, y)).mpr
      ⟨le_of_lt h1, h2, (cross_neg_iff_lt_threshold a b y x (by linarith)).mpr hx⟩
  · rw [if_neg hx]
    rcases edgeWind_mem a b (x, y) with h | h | h
    · exfalso
      have hc : cross (b - a) ((x, y) - a) < 0 := ((edgeWind_eq_neg_one_iff a b (x, y)).mp h).2.2
      exact hx ((cross_neg_iff_lt_threshold a b y x (by linarith)).mp hc)
    · exact h
    · exfalso
      have hh : y < b.2 := (edgeWind_eq_one_imp a b (x, y) h).2
      linarith

/-- An edge **crosses** height `y` (strictly, in either direction) exactly when
its two endpoints lie on opposite sides of the line `{· = y}`. With generic `y`
(no endpoint at height `y`) this is the basis of the traversal-order alternation:
each crossing flips the side, so crossings alternate up/down as one goes around. -/
lemma span_iff_above_ne (a b y : ℝ) (ha : a ≠ y) (hb : b ≠ y) :
    ((a < y ∧ y < b) ∨ (b < y ∧ y < a)) ↔ ((y < a) ≠ (y < b)) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) heq <;> rw [eq_iff_iff] at heq
    · have := heq.mpr h2; linarith
    · have := heq.mp h2; linarith
  · intro h
    rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
    · exact absurd (by rw [eq_iff_iff]; constructor <;> intro <;> linarith) h
    · exact Or.inl ⟨ha', hb'⟩
    · exact Or.inr ⟨hb', ha'⟩
    · exact absurd (by rw [eq_iff_iff]; constructor <;> intro <;> linarith) h

/-- A point at height `y` lies on the edge's line exactly at `x = x*`: the
threshold is the unique crossing `x`. -/
lemma cross_eq_zero_iff_threshold (a b : ℝ × ℝ) (y x : ℝ) (hne : b.2 ≠ a.2) :
    cross (b - a) ((x, y) - a) = 0 ↔ x = crossThreshold a b y := by
  have hd : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · intro h
    unfold cross at h
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    unfold crossThreshold
    field_simp
    linear_combination -h
  · intro h
    rw [h]
    exact cross_crossThreshold a b y hne

/-- Unified per-edge form for a spanning edge: `edgeWind = sign · [x < x*]`, where
`sign = +1` if the edge ascends through `y` (`b` above) and `−1` if it descends.
This is the working summand for `winding = Σ sign·[x < x*]`. -/
lemma edgeWind_spanning_eq (a b : ℝ × ℝ) (x y : ℝ)
    (h : (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)) :
    edgeWind a b (x, y)
      = (if y < b.2 then (1 : ℤ) else -1) * (if x < crossThreshold a b y then 1 else 0) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h2, edgeWind_eq_indicator_up a b y x h1 h2, one_mul]
  · rw [if_neg (not_lt.mpr (le_of_lt h1)), edgeWind_eq_indicator_down a b y x h1 h2]
    split_ifs <;> ring

/-- The crossing `x` lies within the edge's `x`-extent: `(x*−a.1)(x*−b.1) ≤ 0`,
i.e. `x*` is between `a.1` and `b.1`. (Strictly-spanning up-edge.) -/
lemma crossThreshold_between (a b : ℝ × ℝ) (y : ℝ) (h1 : a.2 < y) (h2 : y < b.2) :
    (crossThreshold a b y - a.1) * (crossThreshold a b y - b.1) ≤ 0 := by
  have hd : (0:ℝ) < b.2 - a.2 := by linarith
  have key : (crossThreshold a b y - a.1) * (crossThreshold a b y - b.1)
      = (b.1 - a.1) ^ 2 * (y - a.2) * (y - b.2) / (b.2 - a.2) ^ 2 := by
    unfold crossThreshold; field_simp; ring
  rw [key]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (b.1 - a.1))
      (show (0:ℝ) ≤ y - a.2 by linarith)) (show (0:ℝ) ≤ b.2 - y by linarith)]
  · positivity

/-- Down-orientation companion of `crossThreshold_between`. -/
lemma crossThreshold_between_down (a b : ℝ × ℝ) (y : ℝ) (h1 : b.2 < y) (h2 : y < a.2) :
    (crossThreshold a b y - a.1) * (crossThreshold a b y - b.1) ≤ 0 := by
  rw [crossThreshold_comm a b y (by linarith : a.2 ≠ b.2), mul_comm]
  exact crossThreshold_between b a y h1 h2

/-- Only edges that span height `y` contribute to the winding: a nonzero
`edgeWind` forces the test height into the edge's `y`-range. -/
lemma edgeWind_ne_zero_imp_span (a b : ℝ × ℝ) (x y : ℝ) (h : edgeWind a b (x, y) ≠ 0) :
    (a.2 ≤ y ∧ y < b.2) ∨ (b.2 ≤ y ∧ y < a.2) := by
  rcases edgeWind_mem a b (x, y) with h' | h' | h'
  · exact Or.inr (edgeWind_eq_neg_one_imp a b (x, y) h')
  · exact absurd h' h
  · exact Or.inl (edgeWind_eq_one_imp a b (x, y) h')

/-- Complete per-edge form at a **generic** height `y` (no endpoint at height
`y`): the edge contributes `sign · [x < x*]` if it spans `y`, and `0` otherwise.
The single clean summand for `winding((x,y))` as a step function of `x`. -/
lemma edgeWind_generic (a b : ℝ × ℝ) (x y : ℝ) (ha : a.2 ≠ y) (hb : b.2 ≠ y) :
    edgeWind a b (x, y) =
      if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℤ) else -1) * (if x < crossThreshold a b y then 1 else 0)
      else 0 := by
  by_cases hspan : (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)
  · rw [if_pos hspan]; exact edgeWind_spanning_eq a b x y hspan
  · rw [if_neg hspan]
    by_contra hne
    apply hspan
    rcases edgeWind_ne_zero_imp_span a b x y hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lt_of_le_of_ne h1 ha, h2⟩
    · exact Or.inr ⟨lt_of_le_of_ne h1 hb, h2⟩

/-- The threshold point is on the segment for **either** crossing orientation
(the edge passes strictly through height `y`). -/
lemma crossThreshold_mem_segment_strict (a b : ℝ × ℝ) (y : ℝ)
    (h : (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)) :
    (crossThreshold a b y, y) ∈ segment ℝ a b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact crossThreshold_mem_segment a b y h1 h2
  · exact crossThreshold_mem_segment_down a b y h1 h2

/-- General distinctness: any two non-adjacent edges that both pass strictly
through height `y` (in any orientation) cross the ray at distinct `x`. This makes
the full set of ray-crossings strictly ordered. -/
lemma crossThreshold_ne_of_simple' (P : LatticePolygon) (hP : P.IsSimple) (y : ℝ)
    (i j : ZMod P.n) (hij : i ≠ j) (h1 : i + 1 ≠ j) (h2 : j + 1 ≠ i)
    (hi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    (hj : ((toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2) ∨
          ((toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)) :
    crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y
      ≠ crossThreshold (toReal (P.vert j)) (toReal (P.vert (j + 1))) y := by
  intro heq
  have memi : (crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y, y)
      ∈ P.edgeSeg i := crossThreshold_mem_segment_strict _ _ y hi
  have memj : (crossThreshold (toReal (P.vert j)) (toReal (P.vert (j + 1))) y, y)
      ∈ P.edgeSeg j := crossThreshold_mem_segment_strict _ _ y hj
  rw [heq] at memi
  exact Set.disjoint_left.mp (hP.2.1 i j hij h1 h2) memi memj

/-- **Adjacent-edge distinctness** (uses the third `IsSimple` clause). Two
consecutive edges `i, i+1` that both cross height `y` strictly meet the ray at
distinct `x` — equal thresholds would put the shared crossing at the shared
vertex `vert (i+1)`, whose height is `≠ y`. This is the distinctness needed for a
triangle (whose spanning edges are always adjacent). -/
lemma crossThreshold_ne_of_simple_adj (P : LatticePolygon) (hP : P.IsSimple) (y : ℝ)
    (i : ZMod P.n) (hy : y ≠ (toReal (P.vert (i + 1))).2)
    (hi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    (hj : ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert (i + 1 + 1))).2) ∨
          ((toReal (P.vert (i + 1 + 1))).2 < y ∧ y < (toReal (P.vert (i + 1))).2)) :
    crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y
      ≠ crossThreshold (toReal (P.vert (i + 1))) (toReal (P.vert (i + 1 + 1))) y := by
  intro heq
  have memi : (crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y, y)
      ∈ P.edgeSeg i := crossThreshold_mem_segment_strict _ _ y hi
  have memj : (crossThreshold (toReal (P.vert (i + 1))) (toReal (P.vert (i + 1 + 1))) y, y)
      ∈ P.edgeSeg (i + 1) := crossThreshold_mem_segment_strict _ _ y hj
  rw [heq] at memi
  have hmem : (crossThreshold (toReal (P.vert (i + 1))) (toReal (P.vert (i + 1 + 1))) y, y)
      ∈ P.edgeSeg i ∩ P.edgeSeg (i + 1) := ⟨memi, memj⟩
  rw [hP.2.2 i, Set.mem_singleton_iff] at hmem
  exact hy (congrArg Prod.snd hmem)

/-- The number of up-crossings to the right of `x` is **antitone** in `x`: moving
right, the ray loses up-crossings one threshold at a time. (Companion fact for
down-crossings is monotone.) A step toward the sorted-crossing/alternation
structure: `winding` is built from these monotone counts. -/
lemma upCount_antitone (P : LatticePolygon) (y x1 x2 : ℝ) (hx : x1 ≤ x2) :
    (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x2, y) = 1).card ≤
    (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x1, y) = 1).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨ha, hb⟩ := edgeWind_eq_one_imp _ _ _ hi
  have hanti := edgeWind_up_antitone (toReal (P.vert i)) (toReal (P.vert (i + 1))) y x1 x2 hx ha hb
  rcases edgeWind_mem (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x1, y) with h | h | h
  · rw [hi, h] at hanti; norm_num at hanti
  · rw [hi, h] at hanti; norm_num at hanti
  · exact h

/-- The number of down-crossings to the right of `x` is also **antitone** in `x`.
With `upCount_antitone`, both pieces of `winding = #up − #down` lose crossings as
`x` moves right — `winding` changes only by crossing thresholds. -/
lemma downCount_antitone (P : LatticePolygon) (y x1 x2 : ℝ) (hx : x1 ≤ x2) :
    (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x2, y) = -1).card ≤
    (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x1, y) = -1).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨hb, ha⟩ := edgeWind_eq_neg_one_imp _ _ _ hi
  have hmono := edgeWind_down_monotone (toReal (P.vert i)) (toReal (P.vert (i + 1))) y x1 x2 hx hb ha
  rcases edgeWind_mem (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x1, y) with h | h | h
  · exact h
  · rw [hi, h] at hmono; norm_num at hmono
  · rw [hi, h] at hmono; norm_num at hmono

/-- The winding at a generic height as an explicit signed step-function sum over
edges: each spanning edge contributes `sign · [x < x*]`. This is the closed form
the sweep / Green's-theorem arguments integrate and the alternation squeezes. -/
lemma winding_generic_sum (P : LatticePolygon) (x y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    P.winding (x, y) = ∑ i,
      (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else -1) *
          (if x < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y then 1 else 0)
      else 0) := by
  unfold LatticePolygon.winding
  exact Finset.sum_congr rfl fun i _ => edgeWind_generic _ _ x y (hy i) (hy (i + 1))

/-- **Threshold-based local constancy.** At a generic height, the winding is
unchanged between two `x`-values lying on the same side of every crossing
threshold — it only changes when `x` passes a threshold. -/
lemma winding_eq_of_same_side (P : LatticePolygon) (x1 x2 y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (hsame : ∀ i, (x1 < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y) ↔
                  (x2 < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y)) :
    P.winding (x1, y) = P.winding (x2, y) := by
  rw [winding_generic_sum P x1 y hy, winding_generic_sum P x2 y hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hsp : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)
  · rw [if_pos hsp, if_pos hsp]
    refine congrArg _ ?_
    by_cases hx : x1 < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y
    · rw [if_pos hx, if_pos ((hsame i).mp hx)]
    · rw [if_neg hx, if_neg (fun h => hx ((hsame i).mpr h))]
  · rw [if_neg hsp, if_neg hsp]

/-- The winding at a swept point is the up-crossing count minus the down-crossing
count — both antitone in `x` (`upCount_antitone`, `downCount_antitone`). This is
the explicit step-function the alternation argument squeezes into `{0,1}`. -/
lemma winding_eq_upCount_sub_downCount (P : LatticePolygon) (x y : ℝ) :
    P.winding (x, y) =
      ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card : ℤ) -
      (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card :=
  winding_eq_card_sub P (x, y)

/-- The spanning count is twice the up-crossing count (up- and down-crossings are
disjoint and equinumerous). So `#up = #spanning / 2`. -/
lemma card_spanning_eq_two_mul_up (P : LatticePolygon) (y : ℝ) :
    (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card =
      2 * (Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card := by
  classical
  have hdisj : Disjoint
      (Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2)
      (Finset.univ.filter fun i =>
        (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2) := by
    rw [Finset.disjoint_filter]
    rintro i _ ⟨_, hub⟩ ⟨hdb, _⟩
    linarith
  rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj, ← card_up_eq_card_down, two_mul]

/-- An edge whose endpoints **strictly straddle** `y` lies in the strict spanning
filter (upward case). Used to pin down the two band-1 spanning edges (those incident
to the lowest vertex `L`). -/
lemma mem_strict_spanning_of_lt_up (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (h1 : (toReal (P.vert i)).2 < y) (h2 : y < (toReal (P.vert (i + 1))).2) :
    i ∈ Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl ⟨h1, h2⟩⟩

/-- An edge whose endpoints **strictly straddle** `y` (downward case) lies in the
strict spanning filter. -/
lemma mem_strict_spanning_of_lt_down (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (h1 : (toReal (P.vert (i + 1))).2 < y) (h2 : y < (toReal (P.vert i)).2) :
    i ∈ Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr ⟨h1, h2⟩⟩

/-- **Triangle base case, step 1.** For a triangle (`n = 3`) at any height, the
ray-line crosses `0` or `2` edges — the count is even (`card_spanning_even`) and
at most `3` (≤ number of edges). This anchors the base case of the `winding ∈
{0,1}` induction. -/
lemma spanning_count_triangle (P : LatticePolygon) (hn : P.n = 3) (y : ℝ) :
    (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card = 0 ∨
    (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card = 2 := by
  obtain ⟨k, hk⟩ := card_spanning_even P y
  have hle : (Finset.univ.filter fun i =>
      ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≤ 3 := by
    calc _ ≤ (Finset.univ : Finset (ZMod P.n)).card := Finset.card_filter_le _ _
      _ = P.n := by rw [Finset.card_univ, ZMod.card]
      _ = 3 := hn
  omega

/-- **Triangle base case, step 2.** A triangle has at most one up-crossing of the
ray at any `x`: `#{edgeWind = 1} ≤ #{up-spanning} = #spanning/2 ≤ 1`. -/
lemma upCount_le_one_triangle (P : LatticePolygon) (hn : P.n = 3) (x y : ℝ) :
    (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card ≤ 1 := by
  classical
  have hcard : (Finset.univ.filter fun i =>
      (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card ≤ 1 := by
    have h2 := card_spanning_eq_two_mul_up P y
    have hsp := spanning_count_triangle P hn y
    omega
  refine le_trans (Finset.card_le_card ?_) hcard
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, edgeWind_eq_one_imp _ _ _ hi.2⟩

/-- **Triangle base case, step 3.** A triangle has at most one down-crossing too. -/
lemma downCount_le_one_triangle (P : LatticePolygon) (hn : P.n = 3) (x y : ℝ) :
    (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card ≤ 1 := by
  classical
  have hcard : (Finset.univ.filter fun i =>
      (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2).card ≤ 1 := by
    have h2 := card_spanning_eq_two_mul_up P y
    have hdc := card_up_eq_card_down P y
    have hsp := spanning_count_triangle P hn y
    omega
  refine le_trans (Finset.card_le_card ?_) hcard
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, edgeWind_eq_neg_one_imp _ _ _ hi.2⟩

/-- Where the ray-line misses the polygon entirely (no edge spans height `y`),
the winding is `0`: both crossing counts vanish. -/
lemma winding_zero_of_no_spanning (P : LatticePolygon) (x y : ℝ)
    (hsp : (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card = 0) :
    P.winding (x, y) = 0 := by
  classical
  rw [winding_eq_upCount_sub_downCount]
  have hu : (Finset.univ.filter fun i =>
      edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card ≤
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card := by
    apply Finset.card_le_card
    intro i hi; rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, Or.inl (edgeWind_eq_one_imp _ _ _ hi.2)⟩
  have hd : (Finset.univ.filter fun i =>
      edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card ≤
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card := by
    apply Finset.card_le_card
    intro i hi; rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, Or.inr (edgeWind_eq_neg_one_imp _ _ _ hi.2)⟩
  omega

/-- The winding is `0` below the whole polygon (every vertex strictly above `y`),
since no edge spans that height. -/
lemma winding_zero_of_y_below (P : LatticePolygon) (x y : ℝ)
    (hy : ∀ i, y < (toReal (P.vert i)).2) :
    P.winding (x, y) = 0 := by
  apply winding_zero_of_no_spanning
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact absurd h1 (not_le.mpr (hy i))
  · exact absurd h1 (not_le.mpr (hy (i + 1)))

/-- A nonzero winding forces the ray-line to cross the polygon: some edge spans
height `y`. (Contrapositive of `winding_zero_of_no_spanning`.) -/
lemma exists_spanning_of_winding_ne_zero (P : LatticePolygon) (x y : ℝ)
    (h : P.winding (x, y) ≠ 0) :
    (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 :=
  fun hc => h (winding_zero_of_no_spanning P x y hc)

/-- The winding is `0` above the whole polygon (every vertex strictly below `y`). -/
lemma winding_zero_of_y_above (P : LatticePolygon) (x y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 < y) :
    P.winding (x, y) = 0 := by
  apply winding_zero_of_no_spanning
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rintro (⟨_, h2⟩ | ⟨_, h2⟩)
  · exact absurd h2 (not_lt.mpr (le_of_lt (hy (i + 1))))
  · exact absurd h2 (not_lt.mpr (le_of_lt (hy i)))

/-- **Winding parity.** `winding ≡ #up + #down (mod 2)` — the parity of the
winding equals the parity of the total crossing count (since `−#down ≡ #down`).
This is the precursor to the Jordan parity argument: crossing-count parity
determines inside vs. outside. -/
lemma winding_parity (P : LatticePolygon) (x y : ℝ) :
    P.winding (x, y) % 2 =
      (((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card : ℤ) +
        (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card) % 2 := by
  rw [winding_eq_upCount_sub_downCount]
  omega

/-- General bound: `|winding| ≤ #up-spanning = #spanning/2`. The winding is at
most half the crossing count — the natural bound before the alternation tightens
it to `{0,1}`. -/
lemma abs_winding_le_upCount (P : LatticePolygon) (x y : ℝ) :
    -((Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card : ℤ) ≤ P.winding (x, y) ∧
    P.winding (x, y) ≤
      ((Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card : ℤ) := by
  classical
  have hdc := card_up_eq_card_down P y
  rw [winding_eq_upCount_sub_downCount]
  have hu : (Finset.univ.filter fun i =>
      edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card ≤
      (Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card := by
    apply Finset.card_le_card
    intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, edgeWind_eq_one_imp _ _ _ hi.2⟩
  have hd : (Finset.univ.filter fun i =>
      edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card ≤
      (Finset.univ.filter fun i =>
        (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2).card := by
    apply Finset.card_le_card
    intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, edgeWind_eq_neg_one_imp _ _ _ hi.2⟩
  omega

/-- **Key bound.** Wherever the ray-line crosses at most two edges, the winding
is `−1`, `0`, or `1`: it is `#up − #down` with `#up = #down = #spanning/2 ≤ 1`.
This covers triangles and, more generally, convex polygons — the cases where the
alternation is automatic. (Positive orientation then rules out `−1`.) -/
lemma abs_winding_le_one_of_spanning_le_two (P : LatticePolygon) (x y : ℝ)
    (hsp : (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≤ 2) :
    -1 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1 := by
  classical
  have h2 := card_spanning_eq_two_mul_up P y
  have hdc := card_up_eq_card_down P y
  rw [winding_eq_upCount_sub_downCount]
  have hu : (Finset.univ.filter fun i =>
      edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card ≤
      (Finset.univ.filter fun i =>
        (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2).card := by
    apply Finset.card_le_card
    intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, edgeWind_eq_one_imp _ _ _ hi.2⟩
  have hd : (Finset.univ.filter fun i =>
      edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card ≤
      (Finset.univ.filter fun i =>
        (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2).card := by
    apply Finset.card_le_card
    intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, edgeWind_eq_neg_one_imp _ _ _ hi.2⟩
  omega

/-- **Triangle base case.** For a triangle the winding is `−1`, `0`, or `1`
everywhere (the line crosses 0 or 2 edges). -/
lemma abs_winding_le_one_triangle (P : LatticePolygon) (hn : P.n = 3) (x y : ℝ) :
    -1 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1 := by
  refine abs_winding_le_one_of_spanning_le_two P x y ?_
  rcases spanning_count_triangle P hn y with h | h <;> omega

/-- **The `{0,1}` reduction.** An integer winding that is `≥ 0` and `≤ 1` is `0`
or `1`. So the polygonal Jordan crux `h01` splits into two halves: `winding ≤ 1`
(the crossing bound — have for triangles via `abs_winding_le_one_triangle`) and
`winding ≥ 0` (from positive orientation — the hard half). -/
lemma winding_mem_01_of_nonneg_of_le_one (P : LatticePolygon) (q : ℝ × ℝ)
    (hle : P.winding q ≤ 1) (hnn : 0 ≤ P.winding q) :
    P.winding q = 0 ∨ P.winding q = 1 := by
  omega

/-- **Triangle `h01` reduces to `winding ≥ 0`.** For a triangle `winding ≤ 1`
always (the crossing bound), so the Jordan crux `h01` for `n = 3` follows from the
single nonnegativity fact `0 ≤ winding` (the orientation half). -/
lemma h01_triangle_of_nonneg (P : LatticePolygon) (hn : P.n = 3)
    (hnn : ∀ q : ℝ × ℝ, 0 ≤ P.winding q) :
    ∀ q, P.winding q = 0 ∨ P.winding q = 1 := by
  intro q
  refine winding_mem_01_of_nonneg_of_le_one P q ?_ (hnn q)
  have h := (abs_winding_le_one_triangle P hn q.1 q.2).2
  rwa [Prod.mk.eta] at h

/-- **a.e. triangle `h01` reduces to a.e. `winding ≥ 0`.** Since `winding ≤ 1`
pointwise for a triangle, `winding ∈ {0,1}` almost everywhere follows from
`winding ≥ 0` almost everywhere — feeding `pick_of_two_ae`. -/
lemma h01_ae_of_nonneg_ae_triangle (P : LatticePolygon) (hn : P.n = 3)
    (hnn : ∀ᵐ q ∂MeasureTheory.volume, 0 ≤ P.winding q) :
    ∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1 := by
  filter_upwards [hnn] with q hq
  refine winding_mem_01_of_nonneg_of_le_one P q ?_ hq
  have h := (abs_winding_le_one_triangle P hn q.1 q.2).2
  rwa [Prod.mk.eta] at h

/-- `crossThreshold a b` is continuous in the height `y` (it is affine: division
by the constant `b.2 − a.2`). Needed for the constant-sign argument: the
cross-section value, built from crossing positions, varies continuously in `y`. -/
lemma continuous_crossThreshold (a b : ℝ × ℝ) :
    Continuous (fun y => crossThreshold a b y) := by
  simp only [crossThreshold]; fun_prop

/-- The crossing at the edge's **lower** endpoint height is that endpoint's
`x`-coordinate. -/
lemma crossThreshold_bot (a b : ℝ × ℝ) : crossThreshold a b a.2 = a.1 := by
  simp [crossThreshold]

/-- The crossing `crossThreshold a b y` is **continuous in `y`** (affine: division
is by the constant `b.2 − a.2`). So the slab width is continuous, and at the middle
vertex `M.2` it tends to the non-degenerate (nonzero) gap — giving `c(M.2) ≠ 0`. -/
lemma crossThreshold_continuous (a b : ℝ × ℝ) :
    Continuous (fun y => crossThreshold a b y) := by
  unfold crossThreshold
  fun_prop

/-- A function continuous at `x₀` and positive on a left-interval `(a, x₀)` is
nonnegative at `x₀` (limit of positives). Applied to `c`: positivity on band 1
gives `c(M.2) ≥ 0`, which with `c(M.2) ≠ 0` (non-degeneracy) yields `c(M.2) > 0`. -/
lemma ge_zero_of_continuousAt_pos_left (f : ℝ → ℝ) (a x₀ : ℝ) (hax : a < x₀)
    (hc : ContinuousAt f x₀) (hpos : ∀ y ∈ Set.Ioo a x₀, 0 < f y) : 0 ≤ f x₀ := by
  have hl : Filter.Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds (f x₀)) :=
    hc.continuousWithinAt
  refine ge_of_tendsto hl ?_
  have hmem : Set.Ioo a x₀ ∈ nhdsWithin x₀ (Set.Iio x₀) :=
    mem_nhdsWithin.mpr ⟨Set.Ioi a, isOpen_Ioi, hax, fun z hz => ⟨hz.1, hz.2⟩⟩
  filter_upwards [hmem] with y hy
  exact (hpos y hy).le

/-- Two functions continuous at `x₀` that agree on a left-interval `(a, x₀)` agree
at `x₀` (uniqueness of the left limit). Used to pass the band-1 width formula
`c(y) = t_ℓ(y) − t_{ℓ-1}(y)` to the value at `M.2`. -/
lemma eq_of_continuousAt_eqOn_left (f g : ℝ → ℝ) (a x₀ : ℝ) (hax : a < x₀)
    (hcf : ContinuousAt f x₀) (hcg : ContinuousAt g x₀)
    (heq : ∀ y ∈ Set.Ioo a x₀, f y = g y) : f x₀ = g x₀ := by
  have hl : Filter.Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds (f x₀)) :=
    hcf.continuousWithinAt
  have hlg : Filter.Tendsto g (nhdsWithin x₀ (Set.Iio x₀)) (nhds (g x₀)) :=
    hcg.continuousWithinAt
  have hmem : Set.Ioo a x₀ ∈ nhdsWithin x₀ (Set.Iio x₀) :=
    mem_nhdsWithin.mpr ⟨Set.Ioi a, isOpen_Ioi, hax, fun z hz => ⟨hz.1, hz.2⟩⟩
  have hfg : f =ᶠ[nhdsWithin x₀ (Set.Iio x₀)] g := by
    filter_upwards [hmem] with y hy; exact heq y hy
  exact tendsto_nhds_unique hl (Filter.Tendsto.congr' hfg.symm hlg)

/-- A function continuous at `x₀` and positive there is positive somewhere on every
right-interval `(x₀, b)`. Applied to `c`: `c(M.2) > 0` gives a positive point just
inside band 2, which the band-assembly then spreads over the whole band. -/
lemma exists_pos_right_of_continuousAt_pos (f : ℝ → ℝ) (x₀ b : ℝ) (hxb : x₀ < b)
    (hc : ContinuousAt f x₀) (hpos : 0 < f x₀) : ∃ y ∈ Set.Ioo x₀ b, 0 < f y := by
  have hev : ∀ᶠ y in nhdsWithin x₀ (Set.Ioi x₀), 0 < f y :=
    (hc.eventually (eventually_gt_nhds hpos)).filter_mono nhdsWithin_le_nhds
  have hmem : Set.Ioo x₀ b ∈ nhdsWithin x₀ (Set.Ioi x₀) :=
    mem_nhdsWithin.mpr ⟨Set.Iio b, isOpen_Iio, hxb, fun z hz => ⟨hz.2, hz.1⟩⟩
  obtain ⟨y, hfy, hyi⟩ := (hev.and hmem).exists
  exact ⟨y, hyi, hfy⟩

/-- Right-side mirror of `ge_zero_of_continuousAt_pos_left`: continuous at `x₀` and
positive on `(x₀, b)` ⟹ nonneg at `x₀`. So `c(M.2) ≥ 0` holds whether the initial
positive point sits in band 1 (left) or band 2 (right). -/
lemma ge_zero_of_continuousAt_pos_right (f : ℝ → ℝ) (x₀ b : ℝ) (hxb : x₀ < b)
    (hc : ContinuousAt f x₀) (hpos : ∀ y ∈ Set.Ioo x₀ b, 0 < f y) : 0 ≤ f x₀ := by
  have hl : Filter.Tendsto f (nhdsWithin x₀ (Set.Ioi x₀)) (nhds (f x₀)) :=
    hc.continuousWithinAt
  refine ge_of_tendsto hl ?_
  have hmem : Set.Ioo x₀ b ∈ nhdsWithin x₀ (Set.Ioi x₀) :=
    mem_nhdsWithin.mpr ⟨Set.Iio b, isOpen_Iio, hxb, fun z hz => ⟨hz.2, hz.1⟩⟩
  filter_upwards [hmem] with y hy
  exact (hpos y hy).le

/-- Combine `≥ 0` (left positivity) with `≠ 0` to get strict positivity at `x₀`. So
`c(M.2) > 0` from band-1 positivity (`c ≥ 0` at `M.2`) plus `c(M.2) ≠ 0`. -/
lemma pos_of_continuousAt_pos_left_ne (f : ℝ → ℝ) (a x₀ : ℝ) (hax : a < x₀)
    (hc : ContinuousAt f x₀) (hpos : ∀ y ∈ Set.Ioo a x₀, 0 < f y) (hne : f x₀ ≠ 0) :
    0 < f x₀ :=
  lt_of_le_of_ne (ge_zero_of_continuousAt_pos_left f a x₀ hax hc hpos) (Ne.symm hne)

/-- Right-side mirror: `c(M.2) > 0` from band-2 positivity plus `c(M.2) ≠ 0`. -/
lemma pos_of_continuousAt_pos_right_ne (f : ℝ → ℝ) (x₀ b : ℝ) (hxb : x₀ < b)
    (hc : ContinuousAt f x₀) (hpos : ∀ y ∈ Set.Ioo x₀ b, 0 < f y) (hne : f x₀ ≠ 0) :
    0 < f x₀ :=
  lt_of_le_of_ne (ge_zero_of_continuousAt_pos_right f x₀ b hxb hc hpos) (Ne.symm hne)

/-- The crossing at the edge's **upper** endpoint height is that endpoint's
`x`-coordinate (for a non-horizontal edge). Both incident edges of a vertex `M`
thus cross at `M.1` when `y = M.2` — the basis of the vertex cancellation. -/
lemma crossThreshold_top (a b : ℝ × ℝ) (h : a.2 ≠ b.2) : crossThreshold a b b.2 = b.1 := by
  rw [crossThreshold]
  field_simp
  ring

/-- As `y → b.2`, the crossing of edge `a→b` tends to `b.1` (its top endpoint's
`x`). With the cyclic edge structure this gives the limiting slab width at `M.2`:
the band-1 spanning edges `L→M`, `L→H` have crossings tending to `M.1` and
`crossThreshold L H M.2`, whose nonzero gap is `c(M.2) ≠ 0`. -/
lemma crossThreshold_tendsto_top (a b : ℝ × ℝ) (h : a.2 ≠ b.2) :
    Filter.Tendsto (fun y => crossThreshold a b y) (nhds b.2) (nhds b.1) := by
  rw [← crossThreshold_top a b h]
  exact (crossThreshold_continuous a b).continuousAt

/-- As `y → a.2`, the crossing of edge `a→b` tends to `a.1` (its bottom endpoint's
`x`). Mirror of `crossThreshold_tendsto_top` — used when the middle vertex `M` is an
edge's *first* (lower) endpoint. -/
lemma crossThreshold_tendsto_bot (a b : ℝ × ℝ) :
    Filter.Tendsto (fun y => crossThreshold a b y) (nhds a.2) (nhds a.1) := by
  rw [← crossThreshold_bot a b]
  exact (crossThreshold_continuous a b).continuousAt

/-- The crossing of edge `a→b` at height `c.2` hits exactly `c.1` iff `c` is
collinear with `a, b` (`cross (b−a) (c−a) = 0`). So for a **non-degenerate**
triangle the middle vertex `M` does **not** lie on the opposite edge's crossing,
giving `c(M.2) ≠ 0`. -/
lemma crossThreshold_eq_iff_cross_zero (a b c : ℝ × ℝ) (h : a.2 ≠ b.2) :
    crossThreshold a b c.2 = c.1 ↔ cross (b - a) (c - a) = 0 := by
  have hd : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [crossThreshold, add_div' _ _ _ hd, div_eq_iff hd, cross]
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h2 <;> linear_combination h2

/-- For a **non-collinear** triple (`cross (b−a) (c−a) ≠ 0`), the crossing of edge
`a→b` at height `c.2` misses `c.1`. (At the middle vertex `M` of a non-degenerate
triangle, the opposite edge's crossing thus differs from `M.1`, so `c(M.2) ≠ 0`.) -/
lemma crossThreshold_ne_of_cross_ne_zero (a b c : ℝ × ℝ) (h : a.2 ≠ b.2)
    (hc : cross (b - a) (c - a) ≠ 0) : crossThreshold a b c.2 ≠ c.1 :=
  fun heq => hc ((crossThreshold_eq_iff_cross_zero a b c h).mp heq)

/-- **Constant-sign engine (IVT).** A continuous function that is nonzero
throughout an open interval and positive at one point is positive on the whole
interval. (If it dipped `≤ 0` it would cross `0` by the intermediate value
theorem, contradicting nonvanishing.) This turns "`∫ c > 0` + `c ≠ 0`" into
"`c > 0` pointwise" for the cross-section value. -/
lemma pos_of_continuous_ne_zero_Ioo (f : ℝ → ℝ) (a b : ℝ) (hf : Continuous f)
    (hne : ∀ y ∈ Set.Ioo a b, f y ≠ 0) (y₀ : ℝ) (hy₀ : y₀ ∈ Set.Ioo a b)
    (hpos : 0 < f y₀) (y : ℝ) (hy : y ∈ Set.Ioo a b) : 0 < f y := by
  by_contra hle
  push_neg at hle
  have hneg : f y < 0 := lt_of_le_of_ne hle (hne y hy)
  have h0 : (0 : ℝ) ∈ Set.uIcc (f y₀) (f y) := by
    rw [Set.uIcc_of_ge (le_of_lt (hneg.trans hpos))]
    exact ⟨le_of_lt hneg, le_of_lt hpos⟩
  obtain ⟨z, hz, hfz⟩ := intermediate_value_uIcc hf.continuousOn h0
  exact hne z ((Set.ordConnected_Ioo).uIcc_subset hy₀ hy hz) hfz

/-- `ContinuousOn` variant of the constant-sign engine: positivity propagates
across an open interval on which `f` is continuous and nonvanishing. (The
cross-section value is continuous only *on* the spanning range, not globally.) -/
lemma pos_of_continuousOn_ne_zero_Ioo (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Ioo a b)) (hne : ∀ y ∈ Set.Ioo a b, f y ≠ 0)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Set.Ioo a b) (hpos : 0 < f y₀)
    (y : ℝ) (hy : y ∈ Set.Ioo a b) : 0 < f y := by
  by_contra hle
  push_neg at hle
  have hneg : f y < 0 := lt_of_le_of_ne hle (hne y hy)
  have h0 : (0 : ℝ) ∈ Set.uIcc (f y₀) (f y) := by
    rw [Set.uIcc_of_ge (le_of_lt (hneg.trans hpos))]
    exact ⟨le_of_lt hneg, le_of_lt hpos⟩
  have hsub : Set.uIcc y₀ y ⊆ Set.Ioo a b := (Set.ordConnected_Ioo).uIcc_subset hy₀ hy
  obtain ⟨z, hz, hfz⟩ := intermediate_value_uIcc (hf.mono hsub) h0
  exact hne z (hsub hz) hfz

/-- A left-ray **step function** `y ↦ (if x < g y then c else 0)` is continuous at
`y₀` whenever `x ≠ g y₀` (with `g` continuous there): near `y₀` the strict
inequality `x < g y` is locally constant, so the function is locally constant.
This is the per-edge continuity engine for the vertical local constancy of winding
(each `edgeWind` is such a step in `y`). -/
lemma continuousAt_step (g : ℝ → ℝ) (y₀ x c : ℝ) (hg : ContinuousAt g y₀)
    (hne : x ≠ g y₀) : ContinuousAt (fun y => if x < g y then c else (0 : ℝ)) y₀ := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact continuousAt_const.congr
      ((continuousAt_const.eventually_lt hg h).mono fun y hy => (if_pos hy).symm)
  · exact continuousAt_const.congr
      ((hg.eventually_lt continuousAt_const h).mono fun y hy =>
        (if_neg (not_lt.mpr (le_of_lt hy))).symm)

/-- An **integer-valued continuous** function is locally constant: if `↑g` is
continuous at `y₀` then `g = g y₀` near `y₀`. (Applied to `winding(x, ·)`: it
equals its value at a pass-through vertex `M.2` on a whole neighborhood, so the
sign propagates across `M.2`.) -/
lemma eventually_eq_of_continuousAt_intCast (g : ℝ → ℤ) (y₀ : ℝ)
    (hc : ContinuousAt (fun y => (g y : ℝ)) y₀) :
    ∀ᶠ y in nhds y₀, g y = g y₀ := by
  filter_upwards [Metric.tendsto_nhds.mp hc 1 one_pos] with y hy
  rw [Real.dist_eq] at hy
  have h2 : |g y - g y₀| < 1 := by exact_mod_cast hy
  rw [abs_lt] at h2
  omega

/-- The left-ray step **stabilizes** near `y₀`: when `x ≠ g y₀` (with `g`
continuous), `if x < g y then c else 0` eventually equals its value at `y₀`. The
incident-edge indicators at a vertex thus settle to the common value `[x < M.1]`,
the basis of the regular-vertex cancellation. -/
lemma eventually_step_eq (g : ℝ → ℝ) (y₀ x c : ℝ) (hg : ContinuousAt g y₀) (hne : x ≠ g y₀) :
    ∀ᶠ y in nhds y₀, (if x < g y then c else (0 : ℝ)) = (if x < g y₀ then c else 0) := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [continuousAt_const.eventually_lt hg h] with y hy
    rw [if_pos hy, if_pos h]
  · filter_upwards [hg.eventually_lt continuousAt_const h] with y hy
    rw [if_neg (not_lt.mpr (le_of_lt hy)), if_neg (not_lt.mpr (le_of_lt h))]

/-- **Per-edge vertical continuity (spanning up-edge).** For `a.2 < y₀ < b.2` and
`x ≠ crossThreshold a b y₀`, the cast contribution `y ↦ edgeWind a b (x,y)` is
continuous at `y₀` (near `y₀` it equals the continuous step `[x < crossThreshold]`). -/
lemma edgeWind_real_continuousAt_up (a b : ℝ × ℝ) (x y₀ : ℝ) (h1 : a.2 < y₀) (h2 : y₀ < b.2)
    (hx : x ≠ crossThreshold a b y₀) :
    ContinuousAt (fun y => (edgeWind a b (x, y) : ℝ)) y₀ := by
  have hstep : ContinuousAt (fun y => if x < crossThreshold a b y then (1 : ℝ) else 0) y₀ :=
    continuousAt_step (fun y => crossThreshold a b y) y₀ x 1
      (continuous_crossThreshold a b).continuousAt hx
  refine hstep.congr ?_
  filter_upwards [Ioo_mem_nhds h1 h2] with y hy
  rw [edgeWind_eq_indicator_up a b y x hy.1 hy.2]
  push_cast; rfl

/-- **Per-edge vertical continuity (spanning down-edge).** For `b.2 < y₀ < a.2` and
`x ≠ crossThreshold a b y₀`. -/
lemma edgeWind_real_continuousAt_down (a b : ℝ × ℝ) (x y₀ : ℝ) (h1 : b.2 < y₀) (h2 : y₀ < a.2)
    (hx : x ≠ crossThreshold a b y₀) :
    ContinuousAt (fun y => (edgeWind a b (x, y) : ℝ)) y₀ := by
  have hstep : ContinuousAt (fun y => if x < crossThreshold a b y then (-1 : ℝ) else 0) y₀ :=
    continuousAt_step (fun y => crossThreshold a b y) y₀ x (-1)
      (continuous_crossThreshold a b).continuousAt hx
  refine hstep.congr ?_
  filter_upwards [Ioo_mem_nhds h1 h2] with y hy
  rw [edgeWind_eq_indicator_down a b y x hy.1 hy.2]
  push_cast; rfl

/-- **Per-edge vertical continuity (all cases).** For a height `y₀` that is not an
endpoint of the edge (`y₀ ≠ a.2, b.2`) and `x` off the crossing when the edge
spans, `y ↦ edgeWind a b (x,y)` is continuous at `y₀` (spanning up/down via the
step lemmas; otherwise eventually `0`). -/
lemma edgeWind_real_continuousAt (a b : ℝ × ℝ) (x y₀ : ℝ)
    (hya : y₀ ≠ a.2) (hyb : y₀ ≠ b.2)
    (hx : ((a.2 < y₀ ∧ y₀ < b.2) ∨ (b.2 < y₀ ∧ y₀ < a.2)) → x ≠ crossThreshold a b y₀) :
    ContinuousAt (fun y => (edgeWind a b (x, y) : ℝ)) y₀ := by
  rcases lt_trichotomy y₀ a.2 with ha | ha | ha
  · rcases lt_trichotomy y₀ b.2 with hb | hb | hb
    · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y₀).congr ?_
      filter_upwards [Iio_mem_nhds ha, Iio_mem_nhds hb] with y hy1 hy2
      rw [edgeWind_eq_zero_of_below a b (x, y) hy1 hy2]; simp
    · exact absurd hb hyb
    · exact edgeWind_real_continuousAt_down a b x y₀ hb ha (hx (Or.inr ⟨hb, ha⟩))
  · exact absurd ha hya
  · rcases lt_trichotomy y₀ b.2 with hb | hb | hb
    · exact edgeWind_real_continuousAt_up a b x y₀ ha hb (hx (Or.inl ⟨ha, hb⟩))
    · exact absurd hb hyb
    · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y₀).congr ?_
      filter_upwards [Ioi_mem_nhds ha, Ioi_mem_nhds hb] with y hy1 hy2
      rw [edgeWind_eq_zero_of_above a b (x, y) (le_of_lt hy1) (le_of_lt hy2)]; simp

/-- **Regular-vertex cancellation.** For two edges `(a,m)`, `(m,b)` meeting at `m`
with `a.2 < m.2 < b.2` (so `m` is a "pass-through" vertex), and `x ≠ m.1`, the sum
of their contributions is continuous in `y` at `m.2`: near `m.2` it equals the
constant `[x < m.1]` (the disappearing edge's value is taken over by the appearing
one, both crossing at `m.1`). This is the vertex case of vertical local constancy. -/
lemma edgeWind_pair_continuousAt (a m b : ℝ × ℝ) (x : ℝ) (hab : a.2 < m.2) (hmb : m.2 < b.2)
    (hx : x ≠ m.1) :
    ContinuousAt (fun y => (edgeWind a m (x, y) : ℝ) + (edgeWind m b (x, y) : ℝ)) m.2 := by
  have hm1a : crossThreshold a m m.2 = m.1 := crossThreshold_top a m (ne_of_lt hab)
  have hm1b : crossThreshold m b m.2 = m.1 := crossThreshold_bot m b
  have he1 := eventually_step_eq (fun y => crossThreshold a m y) m.2 x 1
    (continuous_crossThreshold a m).continuousAt (by rw [hm1a]; exact hx)
  have he2 := eventually_step_eq (fun y => crossThreshold m b y) m.2 x 1
    (continuous_crossThreshold m b).continuousAt (by rw [hm1b]; exact hx)
  rw [hm1a] at he1; rw [hm1b] at he2
  refine (continuousAt_const :
    ContinuousAt (fun _ : ℝ => (if x < m.1 then (1 : ℝ) else 0)) m.2).congr ?_
  filter_upwards [Ioo_mem_nhds hab hmb, he1, he2] with y hy hye1 hye2
  rcases lt_trichotomy y m.2 with hlt | heq | hgt
  · rw [edgeWind_eq_indicator_up a m y x hy.1 hlt,
      edgeWind_eq_zero_of_below m b (x, y) hlt (lt_trans hlt hmb)]
    push_cast; rw [hye1]; ring
  · rw [heq, edgeWind_eq_zero_of_above a m (x, m.2) (le_of_lt hab) (le_refl _)]
    by_cases hxm : x < m.1
    · rw [(edgeWind_eq_one_iff m b (x, m.2)).mpr ⟨le_refl _, hmb,
        (cross_pos_iff_lt_threshold m b m.2 x hmb).mpr (hm1b ▸ hxm)⟩]
      simp [hxm]
    · have h0 : edgeWind m b (x, m.2) = 0 := by
        rcases edgeWind_mem m b (x, m.2) with h | h | h
        · exact absurd (edgeWind_eq_neg_one_imp m b (x, m.2) h).1 (not_le.mpr hmb)
        · exact h
        · exact absurd ((cross_pos_iff_lt_threshold m b m.2 x hmb).mp
            ((edgeWind_eq_one_iff m b (x, m.2)).mp h).2.2) (hm1b ▸ hxm)
      rw [h0]; simp [hxm]
  · rw [edgeWind_eq_zero_of_above a m (x, y) (le_of_lt (lt_trans hab hgt)) (le_of_lt hgt),
      edgeWind_eq_indicator_up m b y x hgt hy.2]
    push_cast; rw [hye2]; ring

/-- **Regular-vertex cancellation (descending).** Mirror of
`edgeWind_pair_continuousAt` for `b.2 < m.2 < a.2`: the pair sums to the constant
`-[x < m.1]` near `m.2`. -/
lemma edgeWind_pair_continuousAt_desc (a m b : ℝ × ℝ) (x : ℝ) (hba : b.2 < m.2)
    (ham : m.2 < a.2) (hx : x ≠ m.1) :
    ContinuousAt (fun y => (edgeWind a m (x, y) : ℝ) + (edgeWind m b (x, y) : ℝ)) m.2 := by
  have hm1a : crossThreshold a m m.2 = m.1 := crossThreshold_top a m (ne_of_gt ham)
  have hm1b : crossThreshold m b m.2 = m.1 := crossThreshold_bot m b
  have he1 := eventually_step_eq (fun y => crossThreshold a m y) m.2 x (-1)
    (continuous_crossThreshold a m).continuousAt (by rw [hm1a]; exact hx)
  have he2 := eventually_step_eq (fun y => crossThreshold m b y) m.2 x (-1)
    (continuous_crossThreshold m b).continuousAt (by rw [hm1b]; exact hx)
  rw [hm1a] at he1; rw [hm1b] at he2
  refine (continuousAt_const :
    ContinuousAt (fun _ : ℝ => (if x < m.1 then (-1 : ℝ) else 0)) m.2).congr ?_
  filter_upwards [Ioo_mem_nhds hba ham, he1, he2] with y hy hye1 hye2
  rcases lt_trichotomy y m.2 with hlt | heq | hgt
  · rw [edgeWind_eq_zero_of_below a m (x, y) (lt_trans hlt ham) hlt,
      edgeWind_eq_indicator_down m b y x hy.1 hlt]
    push_cast; rw [hye2]; ring
  · rw [heq, edgeWind_eq_zero_of_above m b (x, m.2) (le_refl _) (le_of_lt hba)]
    by_cases hxm : x < m.1
    · rw [(edgeWind_eq_neg_one_iff a m (x, m.2)).mpr ⟨le_refl _, ham,
        (cross_neg_iff_lt_threshold a m m.2 x ham).mpr (hm1a ▸ hxm)⟩]
      simp [hxm]
    · have h0 : edgeWind a m (x, m.2) = 0 := by
        rcases edgeWind_mem a m (x, m.2) with h | h | h
        · exact absurd ((cross_neg_iff_lt_threshold a m m.2 x ham).mp
            ((edgeWind_eq_neg_one_iff a m (x, m.2)).mp h).2.2) (hm1a ▸ hxm)
        · exact h
        · exact absurd (edgeWind_eq_one_imp a m (x, m.2) h).1 (not_le.mpr ham)
      rw [h0]; simp [hxm]
  · rw [edgeWind_eq_indicator_down a m y x hgt hy.2,
      edgeWind_eq_zero_of_above m b (x, y) (le_of_lt hgt) (le_of_lt (lt_trans hba hgt))]
    push_cast; rw [hye1]; ring

/-- **Winding vertical continuity at a non-vertex height.** If no vertex sits at
height `y₀` and `x` avoids every spanning crossing, then `y ↦ winding(x,y)` is
continuous at `y₀` (a finite sum of per-edge continuities). -/
lemma winding_real_continuousAt_of_not_vertex (P : LatticePolygon) (x y₀ : ℝ)
    (hv : ∀ i, y₀ ≠ (toReal (P.vert i)).2)
    (hx : ∀ i, (((toReal (P.vert i)).2 < y₀ ∧ y₀ < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y₀ ∧ y₀ < (toReal (P.vert i)).2)) →
        x ≠ crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y₀) :
    ContinuousAt (fun y => (P.winding (x, y) : ℝ)) y₀ := by
  have heq : (fun y => (P.winding (x, y) : ℝ))
      = fun y => ∑ i, ((edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) : ℤ) : ℝ) := by
    funext y
    simp only [LatticePolygon.winding, Int.cast_sum]
  rw [heq]
  exact tendsto_finset_sum _ fun i _ =>
    edgeWind_real_continuousAt _ _ x y₀ (hv i) (hv (i + 1)) (hx i)

/-- **Sum-split at a vertex.** Isolate the two edges incident to `vert k`
(`e_{k-1} = (vert(k-1), vert k)` and `e_k = (vert k, vert(k+1))`) from the winding
sum, leaving the non-incident edges. This lets the pass-through cancellation
(`edgeWind_pair_continuousAt`) combine with the per-edge continuities. -/
lemma winding_real_split_pair (P : LatticePolygon) (x y : ℝ) (k : ZMod P.n) (hk : k - 1 ≠ k) :
    (P.winding (x, y) : ℝ)
    = ((edgeWind (toReal (P.vert (k - 1))) (toReal (P.vert k)) (x, y) : ℝ)
        + (edgeWind (toReal (P.vert k)) (toReal (P.vert (k + 1))) (x, y) : ℝ))
      + ∑ i ∈ (Finset.univ.erase (k - 1)).erase k,
          ((edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) : ℤ) : ℝ) := by
  have h1 : (P.winding (x, y) : ℝ)
      = ∑ i, ((edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) : ℤ) : ℝ) := by
    simp only [LatticePolygon.winding, Int.cast_sum]
  rw [h1, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (k - 1)),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hk, Finset.mem_univ k⟩),
    ← add_assoc, sub_add_cancel]

/-- **Winding section continuity at a pass-through vertex (ascending).** At the
height of a vertex `k` whose neighbours straddle it ascending, with `x` off the
vertex `x`-coordinate and off the non-incident crossings, `y ↦ winding(x,y)` is
continuous: the incident pair cancels and the rest are per-edge continuous. -/
lemma winding_section_continuousAt_passthrough_asc (P : LatticePolygon) (x : ℝ) (k : ZMod P.n)
    (hk : k - 1 ≠ k) (h1 : (toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2)
    (h2 : (toReal (P.vert k)).2 < (toReal (P.vert (k + 1))).2)
    (hxk : x ≠ (toReal (P.vert k)).1)
    (hrest : ∀ i ∈ (Finset.univ.erase (k - 1)).erase k,
        (toReal (P.vert k)).2 ≠ (toReal (P.vert i)).2 ∧
        (toReal (P.vert k)).2 ≠ (toReal (P.vert (i + 1))).2 ∧
        ((((toReal (P.vert i)).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert i)).2)) →
          x ≠ crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) (toReal (P.vert k)).2)) :
    ContinuousAt (fun y => (P.winding (x, y) : ℝ)) (toReal (P.vert k)).2 := by
  rw [show (fun y => (P.winding (x, y) : ℝ)) = fun y =>
      (((edgeWind (toReal (P.vert (k - 1))) (toReal (P.vert k)) (x, y) : ℝ)
          + (edgeWind (toReal (P.vert k)) (toReal (P.vert (k + 1))) (x, y) : ℝ))
        + ∑ i ∈ (Finset.univ.erase (k - 1)).erase k,
            ((edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) : ℤ) : ℝ))
      from funext fun y => winding_real_split_pair P x y k hk]
  refine (edgeWind_pair_continuousAt _ _ _ x h1 h2 hxk).add ?_
  exact tendsto_finset_sum _ fun i hi =>
    edgeWind_real_continuousAt _ _ x _ (hrest i hi).1 (hrest i hi).2.1 (hrest i hi).2.2

/-- **Winding section continuity at a pass-through vertex (descending).** Mirror
of the ascending case, using the descending pair cancellation. -/
lemma winding_section_continuousAt_passthrough_desc (P : LatticePolygon) (x : ℝ) (k : ZMod P.n)
    (hk : k - 1 ≠ k) (h1 : (toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2)
    (h2 : (toReal (P.vert k)).2 < (toReal (P.vert (k - 1))).2)
    (hxk : x ≠ (toReal (P.vert k)).1)
    (hrest : ∀ i ∈ (Finset.univ.erase (k - 1)).erase k,
        (toReal (P.vert k)).2 ≠ (toReal (P.vert i)).2 ∧
        (toReal (P.vert k)).2 ≠ (toReal (P.vert (i + 1))).2 ∧
        ((((toReal (P.vert i)).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert i)).2)) →
          x ≠ crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) (toReal (P.vert k)).2)) :
    ContinuousAt (fun y => (P.winding (x, y) : ℝ)) (toReal (P.vert k)).2 := by
  rw [show (fun y => (P.winding (x, y) : ℝ)) = fun y =>
      (((edgeWind (toReal (P.vert (k - 1))) (toReal (P.vert k)) (x, y) : ℝ)
          + (edgeWind (toReal (P.vert k)) (toReal (P.vert (k + 1))) (x, y) : ℝ))
        + ∑ i ∈ (Finset.univ.erase (k - 1)).erase k,
            ((edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) : ℤ) : ℝ))
      from funext fun y => winding_real_split_pair P x y k hk]
  refine (edgeWind_pair_continuousAt_desc _ _ _ x h1 h2 hxk).add ?_
  exact tendsto_finset_sum _ fun i hi =>
    edgeWind_real_continuousAt _ _ x _ (hrest i hi).1 (hrest i hi).2.1 (hrest i hi).2.2

/-- **a.e.-continuity at a pass-through vertex height.** Combining both
orientations with the finite exceptional set (`vert k`'s `x`-coordinate together
with the non-incident crossings), the section is continuous at `(vert k).2` for
a.e. `x`. -/
lemma winding_section_ae_continuousAt_passthrough (P : LatticePolygon) (k : ZMod P.n)
    (hk : k - 1 ≠ k)
    (hpass : ((toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k + 1))).2) ∨
             ((toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k - 1))).2))
    (hdist : ∀ i ∈ (Finset.univ.erase (k - 1)).erase k,
        (toReal (P.vert k)).2 ≠ (toReal (P.vert i)).2 ∧
        (toReal (P.vert k)).2 ≠ (toReal (P.vert (i + 1))).2) :
    ∀ᵐ x ∂MeasureTheory.volume,
      ContinuousAt (fun y => (P.winding (x, y) : ℝ)) (toReal (P.vert k)).2 := by
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null _
    ((insert (toReal (P.vert k)).1 (((Finset.univ.erase (k - 1)).erase k).image
      fun i => crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1)))
        (toReal (P.vert k)).2)).finite_toSet.measure_zero _)
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  by_contra hc
  simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
    Finset.mem_coe, not_or, not_exists, not_and] at hc
  obtain ⟨hxk, hci⟩ := hc
  have hrest : ∀ i ∈ (Finset.univ.erase (k - 1)).erase k,
      (toReal (P.vert k)).2 ≠ (toReal (P.vert i)).2 ∧
      (toReal (P.vert k)).2 ≠ (toReal (P.vert (i + 1))).2 ∧
      ((((toReal (P.vert i)).2 < (toReal (P.vert k)).2 ∧
            (toReal (P.vert k)).2 < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < (toReal (P.vert k)).2 ∧
            (toReal (P.vert k)).2 < (toReal (P.vert i)).2)) →
        x ≠ crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) (toReal (P.vert k)).2) :=
    fun i hi => ⟨(hdist i hi).1, (hdist i hi).2, fun _ heq => hci i hi heq.symm⟩
  rcases hpass with hp | hp
  · exact hx (winding_section_continuousAt_passthrough_asc P x k hk hp.1 hp.2 hxk hrest)
  · exact hx (winding_section_continuousAt_passthrough_desc P x k hk hp.1 hp.2 hxk hrest)

/-- For a.e. `x`, `winding(x, ·)` is **locally constant** at a pass-through vertex
height: it equals its value at `(vert k).2` on a whole neighborhood. So the winding
(hence its sign) propagates across the vertex line from either band. -/
lemma winding_section_eq_near_passthrough (P : LatticePolygon) (k : ZMod P.n)
    (hk : k - 1 ≠ k)
    (hpass : ((toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k + 1))).2) ∨
             ((toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k - 1))).2))
    (hdist : ∀ i ∈ (Finset.univ.erase (k - 1)).erase k,
        (toReal (P.vert k)).2 ≠ (toReal (P.vert i)).2 ∧
        (toReal (P.vert k)).2 ≠ (toReal (P.vert (i + 1))).2) :
    ∀ᵐ x ∂MeasureTheory.volume,
      ∀ᶠ y in nhds (toReal (P.vert k)).2,
        P.winding (x, y) = P.winding (x, (toReal (P.vert k)).2) := by
  filter_upwards [winding_section_ae_continuousAt_passthrough P k hk hpass hdist] with x hx
  exact eventually_eq_of_continuousAt_intCast (fun y => P.winding (x, y)) _ hx

/-- **a.e.-continuity at a non-vertex height.** For `y₀` not a vertex height, the
section `winding(x,·)` is continuous at `y₀` for a.e. `x` — the exceptional `x`
(the finitely many crossing positions at height `y₀`) form a null set. -/
lemma winding_section_ae_continuousAt_of_not_vertex (P : LatticePolygon) (y₀ : ℝ)
    (hv : ∀ i, y₀ ≠ (toReal (P.vert i)).2) :
    ∀ᵐ x ∂MeasureTheory.volume, ContinuousAt (fun y => (P.winding (x, y) : ℝ)) y₀ := by
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null _
    ((Finset.univ.image fun i =>
      crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y₀).finite_toSet.measure_zero _)
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  by_contra hc
  rw [Finset.coe_image] at hc
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and, not_exists] at hc
  exact hx (winding_real_continuousAt_of_not_vertex P x y₀ hv (fun i _ heq => hc i heq.symm))

/-- Sum over `ZMod 3` expands to three terms (`ZMod 3` is `Fin 3`). -/
lemma sum_zmod3 {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) :
    (∑ i, f i) = f 0 + f 1 + f 2 := Fin.sum_univ_three f

/-- Corner-cross expansion (bilinearity): `cross (b−a) (c−a) = cross a b + cross b c
+ cross c a`. For a triangle the right side is the cyclic cross-sum `= 2·shoelace`,
so the corner cross equals `2·shoelace` (nonzero for positive orientation). -/
lemma cross_corner_eq (a b c : ℝ × ℝ) :
    cross (b - a) (c - a) = cross a b + cross b c + cross c a := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- Corner cross is **alternating** under base change: swapping the base vertex
negates it. With the cyclic version every corner cross of `{a,b,c}` is `±` the
others, so non-collinearity is permutation-invariant — needed to transfer the
oriented corner-cross to the height-sorted `L,M,H`. -/
lemma cross_corner_swap (a b c : ℝ × ℝ) :
    cross (a - b) (c - b) = -cross (b - a) (c - a) := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- Corner cross is **invariant** under cyclic rotation of the base vertex. -/
lemma cross_corner_cycle (a b c : ℝ × ℝ) :
    cross (c - b) (a - b) = cross (b - a) (c - a) := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **Corner cross = 2·shoelace** for a triangle. With `cross_corner_eq` this gives
the non-degeneracy: positive orientation (`shoelace > 0`) ⟹ `cross(v₁−v₀,v₂−v₀) > 0`
⟹ the three vertices are non-collinear. -/
lemma corner_cross_eq_two_shoelace_triangle (P : LatticePolygon) (hn : P.n = 3) :
    cross (toReal (P.vert 1) - toReal (P.vert 0)) (toReal (P.vert 2) - toReal (P.vert 0))
      = 2 * P.shoelace := by
  obtain ⟨n, pos, vert⟩ := P
  subst hn
  rw [cross_corner_eq, LatticePolygon.shoelace, sum_zmod3,
    show ((0 : ZMod 3) + 1) = 1 from by decide, show ((1 : ZMod 3) + 1) = 2 from by decide,
    show ((2 : ZMod 3) + 1) = 0 from by decide]
  ring

/-- `ZMod 3` is exactly `{ℓ-1, ℓ, ℓ+1}` for any `ℓ`. -/
lemma zmod3_univ_eq_triple : ∀ ℓ : ZMod 3,
    (Finset.univ : Finset (ZMod 3)) = {ℓ - 1, ℓ, ℓ + 1} := by decide

lemma zmod3_sub_one_notMem : ∀ ℓ : ZMod 3, ℓ - 1 ∉ ({ℓ, ℓ + 1} : Finset (ZMod 3)) := by decide

lemma zmod3_notMem_singleton : ∀ ℓ : ZMod 3, ℓ ∉ ({ℓ + 1} : Finset (ZMod 3)) := by decide

lemma zmod3_add_one_add_one : ∀ ℓ : ZMod 3, (ℓ + 1) + 1 = ℓ - 1 := by decide

lemma zmod3_sub_one_sub_one : ∀ ℓ : ZMod 3, (ℓ - 1) - 1 = ℓ + 1 := by decide

/-- For `ZMod 3`, erasing a vertex `k` and its predecessor `k-1` leaves just the
successor `{k+1}` — the single "other" vertex in the pass-through continuity
hypothesis at the middle vertex. -/
lemma zmod3_erase_two : ∀ k : ZMod 3,
    ((Finset.univ.erase (k - 1)).erase k) = {k + 1} := by decide

/-- **Corner cross at an arbitrary base `= 2·shoelace`.** The lowest vertex `L =
vert ℓ` can sit at any cyclic index, so the relevant corner cross is based at the
neighbor `ℓ-1`; for a triangle it still equals `2·shoelace` (the cyclic cross-sum is
base-independent). Hence it is nonzero for positive orientation. -/
lemma corner_cross_base_eq_two_shoelace (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) :
    cross (toReal (P.vert ℓ) - toReal (P.vert (ℓ - 1)))
          (toReal (P.vert (ℓ + 1)) - toReal (P.vert (ℓ - 1))) = 2 * P.shoelace := by
  obtain ⟨n, pos, vert⟩ := P
  subst hn
  rw [cross_corner_eq, LatticePolygon.shoelace, zmod3_univ_eq_triple ℓ,
    Finset.sum_insert (zmod3_sub_one_notMem ℓ), Finset.sum_insert (zmod3_notMem_singleton ℓ),
    Finset.sum_singleton, sub_add_cancel, zmod3_add_one_add_one ℓ]
  ring

/-- The base-`ℓ-1` corner cross is **positive** for a positively-oriented triangle —
the non-degeneracy at the lowest vertex `L = vert ℓ`, whatever index `ℓ` it has. -/
lemma corner_cross_base_pos (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (ℓ : ZMod P.n) :
    0 < cross (toReal (P.vert ℓ) - toReal (P.vert (ℓ - 1)))
          (toReal (P.vert (ℓ + 1)) - toReal (P.vert (ℓ - 1))) := by
  rw [corner_cross_base_eq_two_shoelace P hn ℓ]
  exact mul_pos two_pos horient

/-- **Non-degeneracy from positive orientation.** A positively-oriented triangle
has positive corner cross product, so its three vertices are non-collinear — the
geometric input the cross-band needs. -/
lemma corner_cross_pos_triangle (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) :
    0 < cross (toReal (P.vert 1) - toReal (P.vert 0)) (toReal (P.vert 2) - toReal (P.vert 0)) := by
  rw [corner_cross_eq_two_shoelace_triangle P hn]
  exact mul_pos two_pos horient

/-- The cross product of two lattice points is an integer (cast to `ℝ`). Hence
corner areas / shoelace contributions are half-integers — the lattice fact behind
Pick's `/2`. -/
lemma cross_toReal_int (a b : Pt) :
    cross (toReal a) (toReal b) = ((a.1 * b.2 - a.2 * b.1 : ℤ) : ℝ) := by
  unfold cross toReal
  push_cast
  ring

/-- The cyclic cross-sum is twice the shoelace (signed area). Positive
orientation `shoelace > 0` thus means `∑ cross > 0`. -/
lemma sum_cross_eq_two_shoelace (P : LatticePolygon) :
    (∑ i, cross (toReal (P.vert i)) (toReal (P.vert (i + 1)))) = 2 * P.shoelace := by
  unfold LatticePolygon.shoelace
  ring

/-- `2·shoelace` is an integer: the signed area of a lattice polygon is a
half-integer. This is the lattice fact underlying the `/2` in Pick's formula. -/
lemma two_shoelace_int (P : LatticePolygon) :
    2 * P.shoelace =
      ((∑ i, ((P.vert i).1 * (P.vert (i + 1)).2 - (P.vert i).2 * (P.vert (i + 1)).1) : ℤ) : ℝ) := by
  rw [← sum_cross_eq_two_shoelace, Int.cast_sum]
  exact Finset.sum_congr rfl fun i _ => cross_toReal_int (P.vert i) (P.vert (i + 1))

/-- A positively-oriented lattice polygon has `2·shoelace ≥ 1`, i.e. signed area
`≥ 1/2`: since `2·shoelace` is a positive integer. This is the minimal
lattice-polygon area, consistent with Pick (`I=0, B=3` ⟹ area `1/2`). -/
lemma two_shoelace_ge_one (P : LatticePolygon) (h : P.PositivelyOriented) :
    1 ≤ 2 * P.shoelace := by
  have h2 : 0 < 2 * P.shoelace := by unfold LatticePolygon.PositivelyOriented at h; linarith
  rw [two_shoelace_int] at h2 ⊢
  have hn : 0 < (∑ i, ((P.vert i).1 * (P.vert (i + 1)).2 - (P.vert i).2 * (P.vert (i + 1)).1) : ℤ) := by
    exact_mod_cast h2
  have hn1 : (1 : ℤ) ≤ (∑ i, ((P.vert i).1 * (P.vert (i + 1)).2 - (P.vert i).2 * (P.vert (i + 1)).1)) := by
    omega
  exact_mod_cast hn1

/-- The **corner turn** at vertex `i` (the cross product of the incoming and
outgoing edge vectors) equals twice the signed area of the corner triangle
`(vᵢ₋₁, vᵢ, vᵢ₊₁)`. Its sign is the convexity/orientation of the corner — the
basis for the convex-vertex / ear arguments of the Hopf (turning-number) route. -/
lemma turn_eq_cornerArea (P : LatticePolygon) (i : ZMod P.n) :
    cross (toReal (P.vert i) - toReal (P.vert (i - 1)))
        (toReal (P.vert (i + 1)) - toReal (P.vert i))
      = cross (toReal (P.vert (i - 1))) (toReal (P.vert i))
        + cross (toReal (P.vert i)) (toReal (P.vert (i + 1)))
        + cross (toReal (P.vert (i + 1))) (toReal (P.vert (i - 1))) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **Ear-induction, step 1.** A polygon has a lowest vertex (minimal `y`). The
lowest vertex — broken left — is a convex corner, the seed of the convex-vertex /
two-ears argument for Hopf's turning-number route to `winding ∈ {0,1}`. -/
lemma exists_lowest_vertex (P : LatticePolygon) :
    ∃ m : ZMod P.n, ∀ j, (toReal (P.vert m)).2 ≤ (toReal (P.vert j)).2 := by
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ
    (fun i => (toReal (P.vert i)).2) ⟨0, Finset.mem_univ 0⟩
  exact ⟨m, fun j => hm j (Finset.mem_univ j)⟩

/-- A **highest vertex** exists (the top endpoint of the spanning range). -/
lemma exists_highest_vertex (P : LatticePolygon) :
    ∃ M : ZMod P.n, ∀ j, (toReal (P.vert j)).2 ≤ (toReal (P.vert M)).2 := by
  obtain ⟨M, _, hM⟩ := Finset.exists_max_image Finset.univ
    (fun i => (toReal (P.vert i)).2) ⟨0, Finset.mem_univ 0⟩
  exact ⟨M, fun j => hM j (Finset.mem_univ j)⟩

/-- In `ZMod 3` the **middle** index is forced once lowest `L` and highest `H` are
fixed: any third index equals `-L-H`. (Used to name the middle vertex `M` of a
triangle in the instantiation.) -/
lemma zmod3_third : ∀ L H j : ZMod 3, L ≠ H → j ≠ L → j ≠ H → j = -L - H := by decide

/-- In `ZMod 3`, a vertex differs from its predecessor (`ℓ-1 ≠ ℓ`): the two edges at
`L` (indices `ℓ-1`, `ℓ`) are distinct, so `{ℓ-1, ℓ}` has card 2. -/
lemma zmod3_sub_one_ne : ∀ ℓ : ZMod 3, ℓ - 1 ≠ ℓ := by decide

/-- In `ZMod 3`, every index is one of `ℓ`'s three positions `{ℓ-1, ℓ, ℓ+1}` — i.e.
the triangle's vertices are exactly `L` and its two neighbors. Lets the band-edge
genericity (`y ≠` every vertex height) follow from `y ≠` the three neighbor
heights. -/
lemma zmod3_neighbor_cases : ∀ ℓ i : ZMod 3, i = ℓ - 1 ∨ i = ℓ ∨ i = ℓ + 1 := by decide

/-- **Ear-induction, step 2.** At a lowest vertex, both neighbors lie at or above
it. This is the seed configuration: the corner there opens upward, so it is
convex (the cross-sign / orientation argument is the next step). -/
lemma exists_lowest_vertex_neighbors (P : LatticePolygon) :
    ∃ m : ZMod P.n,
      (toReal (P.vert m)).2 ≤ (toReal (P.vert (m - 1))).2 ∧
      (toReal (P.vert m)).2 ≤ (toReal (P.vert (m + 1))).2 := by
  obtain ⟨m, hm⟩ := exists_lowest_vertex P
  exact ⟨m, hm (m - 1), hm (m + 1)⟩

/-- **Ear-induction, step 3.** There is a lexicographically-lowest vertex
(minimal `y`, then minimal `x`). This specific vertex is provably convex (its
corner turn has the sign of the orientation) — the next step is that cross-sign
argument, which uses the simple + oriented structure. -/
lemma exists_lex_lowest_vertex (P : LatticePolygon) :
    ∃ m : ZMod P.n, ∀ j,
      toLex ((P.vert m).2, (P.vert m).1) ≤ toLex ((P.vert j).2, (P.vert j).1) := by
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ
    (fun i => toLex ((P.vert i).2, (P.vert i).1)) ⟨0, Finset.mem_univ 0⟩
  exact ⟨m, fun j => hm j (Finset.mem_univ j)⟩

/-- The polygon boundary is compact: a finite union of (compact) edge segments. -/
lemma boundary_isCompact (P : LatticePolygon) : IsCompact P.boundary := by
  unfold LatticePolygon.boundary LatticePolygon.edgeSeg
  refine isCompact_iUnion fun i => ?_
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-- The polygon boundary is closed (a consequence of compactness). -/
lemma boundary_isClosed (P : LatticePolygon) : IsClosed P.boundary :=
  (boundary_isCompact P).isClosed

/-- Interior lattice points map into the interior region (where `winding = 1`).
Connects the count side `I` to the area side `interiorRegion`. -/
lemma interiorLattice_toReal_mem (P : LatticePolygon) {q : Pt}
    (hq : q ∈ P.interiorLattice) : toReal q ∈ P.interiorRegion :=
  hq.1

/-- The interior lattice points are exactly the lattice points landing in the
interior region and off the boundary — the count/area dictionary. -/
lemma interiorLattice_eq (P : LatticePolygon) :
    P.interiorLattice = {q | toReal q ∈ P.interiorRegion ∧ toReal q ∉ P.boundary} := rfl

/-- The whole winding support `{winding ≠ 0}` is bounded (not just the `=1`
level): the four directional far-field lemmas confine it to the vertices' Icc.
Toward integrability of `winding` for the area-integral side of Step 2. -/
theorem windingSupport_bounded (P : LatticePolygon) :
    Bornology.IsBounded {q : ℝ × ℝ | P.winding q ≠ 0} := by
  classical
  have hne : (Finset.univ.image (fun i => (P.vert i).1)).Nonempty :=
    Finset.univ_nonempty.image _
  have hne2 : (Finset.univ.image (fun i => (P.vert i).2)).Nonempty :=
    Finset.univ_nonempty.image _
  set xm := (Finset.univ.image (fun i => (P.vert i).1)).min' hne
  set xM := (Finset.univ.image (fun i => (P.vert i).1)).max' hne
  set ym := (Finset.univ.image (fun i => (P.vert i).2)).min' hne2
  set yM := (Finset.univ.image (fun i => (P.vert i).2)).max' hne2
  have hxm : ∀ i, xm ≤ (P.vert i).1 := fun i =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hxM : ∀ i, (P.vert i).1 ≤ xM := fun i =>
    Finset.le_max' (Finset.univ.image (fun j => (P.vert j).1)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hym : ∀ i, ym ≤ (P.vert i).2 := fun i =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hyM : ∀ i, (P.vert i).2 ≤ yM := fun i =>
    Finset.le_max' (Finset.univ.image (fun j => (P.vert j).2)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine (isCompact_Icc (a := (((xm : ℝ), (ym : ℝ)) : ℝ × ℝ))
    (b := ((xM : ℝ), (yM : ℝ)))).isBounded.subset ?_
  intro q hw
  have hw : P.winding q ≠ 0 := hw
  have ha : ∃ i, q.2 < ((P.vert i).2 : ℝ) := by
    by_contra hc; push_neg at hc; exact hw (winding_eq_zero_of_above P q hc)
  have hb : ∃ i, ((P.vert i).2 : ℝ) ≤ q.2 := by
    by_contra hc; push_neg at hc; exact hw (winding_eq_zero_of_below P q hc)
  have hr : ∃ i, q.1 ≤ ((P.vert i).1 : ℝ) := by
    by_contra hc; push_neg at hc; exact hw (winding_eq_zero_of_right P q hc)
  have hl : ∃ i, ((P.vert i).1 : ℝ) ≤ q.1 := by
    by_contra hc; push_neg at hc; exact hw (winding_eq_zero_of_left P q hc)
  obtain ⟨ia, hia⟩ := ha; obtain ⟨ib, hib⟩ := hb
  obtain ⟨ir, hir⟩ := hr; obtain ⟨il, hil⟩ := hl
  simp only [Set.mem_Icc, Prod.le_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast hxm il) hil
  · exact le_trans (by exact_mod_cast hym ib) hib
  · exact le_trans hir (by exact_mod_cast hxM ir)
  · exact le_trans (le_of_lt hia) (by exact_mod_cast hyM ia)

/-- The real-valued winding `q ↦ (winding q : ℝ)` is measurable. -/
lemma measurable_winding_real (P : LatticePolygon) :
    Measurable (fun q => (P.winding q : ℝ)) := by
  have h := measurable_winding P
  measurability

/-- The winding support has finite Lebesgue measure (it is bounded). With
`|winding| ≤ n` and measurability, this gives integrability of `winding`. -/
theorem windingSupport_volume_ne_top (P : LatticePolygon) :
    MeasureTheory.volume {q : ℝ × ℝ | P.winding q ≠ 0} ≠ ⊤ :=
  (windingSupport_bounded P).measure_lt_top.ne

/-- The winding (as a real function) is **integrable**: bounded by `n`, supported
on a finite-measure set, measurable. The area-integral side of Step 2 (`∫∫
winding`) is therefore well-defined. -/
theorem winding_integrable (P : LatticePolygon) :
    MeasureTheory.Integrable (fun q => (P.winding q : ℝ)) := by
  have hS : MeasurableSet {q : ℝ × ℝ | P.winding q ≠ 0} :=
    (measurable_winding P (measurableSet_singleton 0)).compl
  have hSμ : MeasureTheory.volume {q : ℝ × ℝ | P.winding q ≠ 0} < ⊤ :=
    lt_top_iff_ne_top.mpr (windingSupport_volume_ne_top P)
  refine MeasureTheory.Integrable.mono'
    (g := {q : ℝ × ℝ | P.winding q ≠ 0}.indicator (fun _ => (P.n : ℝ)))
    ?_ (measurable_winding_real P).aestronglyMeasurable ?_
  · rw [MeasureTheory.integrable_indicator_iff hS]
    haveI : Fact (MeasureTheory.volume {q : ℝ × ℝ | P.winding q ≠ 0} < ⊤) := ⟨hSμ⟩
    exact MeasureTheory.integrable_const _
  · filter_upwards with q
    by_cases hq : P.winding q = 0
    · simp [hq, Set.indicator_apply]
    · rw [Set.indicator_of_mem hq, Real.norm_eq_abs, ← Int.cast_abs]
      exact_mod_cast abs_winding_le P q

/-- **Reduction of Step 2's `area = ∫∫ winding` to the Jordan hypothesis.** If the
winding is everywhere `0` or `1`, then it equals the indicator of the interior
region, so its integral is exactly the area. This isolates `winding ∈ {0,1}` as
the one missing ingredient (the rest is then Green's `∫∫ winding = shoelace`). -/
theorem area_eq_integral_of_mem01 (P : LatticePolygon)
    (h01 : ∀ q, P.winding q = 0 ∨ P.winding q = 1) :
    P.area = ∫ q, (P.winding q : ℝ) := by
  have hfun : (fun q => (P.winding q : ℝ)) = P.interiorRegion.indicator (fun _ => (1 : ℝ)) := by
    funext q
    simp only [Set.indicator_apply, LatticePolygon.interiorRegion, Set.mem_setOf_eq]
    rcases h01 q with h | h <;> simp [h]
  rw [hfun, MeasureTheory.integral_indicator_const 1 (interiorRegion_measurableSet P),
    smul_eq_mul, mul_one]
  rfl

/-- **a.e. version.** `area = ∫∫ winding` already holds when `winding ∈ {0,1}`
*almost everywhere* — the boundary and vertex-lines are Lebesgue-null, so the
pointwise Jordan hypothesis is unnecessary. This lets the triangle base case
ignore the `M.2` / edge boundary entirely (only generic interior points matter). -/
theorem area_eq_integral_of_mem01_ae (P : LatticePolygon)
    (h01 : ∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1) :
    P.area = ∫ q, (P.winding q : ℝ) := by
  have hfun : (fun q => (P.winding q : ℝ))
      =ᵐ[MeasureTheory.volume] P.interiorRegion.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [h01] with q hq
    simp only [Set.indicator_apply, LatticePolygon.interiorRegion, Set.mem_setOf_eq]
    rcases hq with h | h <;> simp [h]
  rw [MeasureTheory.integral_congr_ae hfun,
    MeasureTheory.integral_indicator_const 1 (interiorRegion_measurableSet P), smul_eq_mul, mul_one]
  rfl

/-- **Master assembly.** Pick's theorem follows from its three remaining
ingredients, cleanly isolated:
* `h01`  — `winding ∈ {0,1}` (the polygonal Jordan crux);
* `hgreen` — `∫∫ winding = shoelace` (Green's theorem, Jordan-free);
* `hcount` — `shoelace = I + B/2 − 1` (Step 1 `shoelace = Σᶠ ŵ` plus the count
  classification `Σᶠ ŵ = I + B/2 − 1`).
This is the entire proof structure, sorry-free given the three hypotheses; it
pins down exactly what remains. -/
theorem pick_of_hypotheses (P : LatticePolygon)
    (h01 : ∀ q, P.winding q = 0 ∨ P.winding q = 1)
    (hgreen : ∫ q, (P.winding q : ℝ) = P.shoelace)
    (hcount : P.shoelace = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 := by
  rw [area_eq_integral_of_mem01 P h01, hgreen, hcount]

/-- **a.e. master assembly.** Same as `pick_of_hypotheses` but only needs the
Jordan hypothesis `winding ∈ {0,1}` *almost everywhere* — what the triangle base
case (and ear-clipping) can actually deliver, the boundary being null. -/
theorem pick_of_hypotheses_ae (P : LatticePolygon)
    (h01 : ∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1)
    (hgreen : ∫ q, (P.winding q : ℝ) = P.shoelace)
    (hcount : P.shoelace = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 := by
  rw [area_eq_integral_of_mem01_ae P h01, hgreen, hcount]

/-- **Green's theorem, brick 1.** For fixed `y`, the cross-section `x`-support
`{x | winding (x,y) ≠ 0}` is bounded (the winding vanishes far left/right). The
first step toward integrability of the cross-section, for the Fubini computation
`∫∫ winding = shoelace`. -/
lemma crossSection_support_bounded (P : LatticePolygon) (y : ℝ) :
    Bornology.IsBounded {x : ℝ | P.winding (x, y) ≠ 0} := by
  classical
  have hne : (Finset.univ.image (fun i => (P.vert i).1)).Nonempty :=
    Finset.univ_nonempty.image _
  set xm := (Finset.univ.image (fun i => (P.vert i).1)).min' hne
  set xM := (Finset.univ.image (fun i => (P.vert i).1)).max' hne
  have hxm : ∀ i, xm ≤ (P.vert i).1 := fun i =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hxM : ∀ i, (P.vert i).1 ≤ xM := fun i =>
    Finset.le_max' (Finset.univ.image (fun j => (P.vert j).1)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine (Metric.isBounded_Icc (xm : ℝ) (xM : ℝ)).subset ?_
  intro x hw
  have hw : P.winding (x, y) ≠ 0 := hw
  have hr : ∃ i, x ≤ ((P.vert i).1 : ℝ) := by
    by_contra hc; push_neg at hc; exact hw (winding_eq_zero_of_right P (x, y) hc)
  have hl : ∃ i, ((P.vert i).1 : ℝ) ≤ x := by
    by_contra hc; push_neg at hc; exact hw (winding_eq_zero_of_left P (x, y) hc)
  obtain ⟨ir, hir⟩ := hr; obtain ⟨il, hil⟩ := hl
  simp only [Set.mem_Icc]
  exact ⟨le_trans (by exact_mod_cast hxm il) hil, le_trans hir (by exact_mod_cast hxM ir)⟩

/-- The cross-section `x ↦ winding (x,y)` is measurable (composition of the
measurable winding with the embedding `x ↦ (x,y)`). Reusable for Fubini. -/
lemma measurable_crossSection (P : LatticePolygon) (y : ℝ) :
    Measurable (fun x => (P.winding (x, y) : ℝ)) :=
  (measurable_winding_real P).comp (by fun_prop)

/-- The interior-slab section `{x | winding (x,y) = 1}` is measurable (the winding
section is measurable). Used to express `c(y)` as the slab measure. -/
lemma measurableSet_winding_section_one (P : LatticePolygon) (y : ℝ) :
    MeasurableSet {x : ℝ | P.winding (x, y) = 1} :=
  ((measurable_winding P).comp (by fun_prop : Measurable fun x => ((x, y) : ℝ × ℝ)))
    (measurableSet_singleton 1)

/-- **Green's theorem, brick 2.** For fixed `y`, the cross-section `x ↦ winding
(x,y)` is integrable (bounded by `n`, bounded support, measurable). Needed for the
inner integral of Fubini. -/
lemma crossSection_integrable (P : LatticePolygon) (y : ℝ) :
    MeasureTheory.Integrable (fun x => (P.winding (x, y) : ℝ)) := by
  have hslice : Measurable (fun x => P.winding (x, y)) :=
    (measurable_winding P).comp (by fun_prop)
  have hmeas : Measurable (fun x => (P.winding (x, y) : ℝ)) :=
    (measurable_winding_real P).comp (by fun_prop)
  have hS : MeasurableSet {x : ℝ | P.winding (x, y) ≠ 0} :=
    (hslice (measurableSet_singleton 0)).compl
  have hSμ : MeasureTheory.volume {x : ℝ | P.winding (x, y) ≠ 0} < ⊤ :=
    (crossSection_support_bounded P y).measure_lt_top
  refine MeasureTheory.Integrable.mono'
    (g := {x : ℝ | P.winding (x, y) ≠ 0}.indicator (fun _ => (P.n : ℝ)))
    ?_ hmeas.aestronglyMeasurable ?_
  · rw [MeasureTheory.integrable_indicator_iff hS]
    haveI : Fact (MeasureTheory.volume {x : ℝ | P.winding (x, y) ≠ 0} < ⊤) := ⟨hSμ⟩
    exact MeasureTheory.integrable_const _
  · filter_upwards with x
    by_cases hx : P.winding (x, y) = 0
    · simp [hx, Set.indicator_apply]
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, ← Int.cast_abs]
      exact_mod_cast abs_winding_le P (x, y)

/-- **Green's theorem, brick (Fubini).** The 2-D winding integral decomposes into
iterated cross-section integrals. Reduces `∫∫ winding` to the cross-section value
`∫_x winding(x,y) dx` integrated over `y`. -/
lemma winding_integral_fubini (P : LatticePolygon) :
    (∫ q, (P.winding q : ℝ)) = ∫ x, ∫ y, (P.winding (x, y) : ℝ) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.integral_prod _
    (by rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]; exact winding_integrable P)

/-- `y`-outer Fubini: `∫∫ winding = ∫_y (∫_x winding(x,y) dx) dy`, so the
cross-section value (which fixes `y`) can be plugged into the inner integral. -/
lemma winding_integral_fubini' (P : LatticePolygon) :
    (∫ q, (P.winding q : ℝ)) = ∫ y, ∫ x, (P.winding (x, y) : ℝ) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.integral_prod_symm _
    (by rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]; exact winding_integrable P)

/-- **Green's theorem, brick (interval integral).** The integral of the indicator
of `[b, a)` is its length `a − b`. This computes the per-threshold contribution to
the cross-section value `∫_x winding dx`. -/
lemma integral_indicator_Ico (a b : ℝ) (h : b ≤ a) :
    (∫ x, (Set.Ico b a).indicator (fun _ => (1 : ℝ)) x) = a - b := by
  rw [MeasureTheory.integral_indicator_const 1 measurableSet_Ico, smul_eq_mul, mul_one]
  exact Real.volume_real_Ico_of_le h

/-- **Green's theorem, brick (telescope).** The cyclic corner-product terms
cancel. This is the algebraic step reducing Green's per-edge `y`-integral sum
`∑ (b.2−a.2)(a.1+b.1)/2` to the shoelace `½ ∑ cross`. -/
lemma sum_corner_telescope (P : LatticePolygon) :
    (∑ i, ((toReal (P.vert i)).1 * (toReal (P.vert i)).2
         - (toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2)) = 0 := by
  rw [Finset.sum_sub_distrib]
  have reindex : (∑ i, (toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2)
               = ∑ i, (toReal (P.vert i)).1 * (toReal (P.vert i)).2 :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n))
      (fun i => (toReal (P.vert i)).1 * (toReal (P.vert i)).2)
  rw [reindex, sub_self]

/-- **Green's theorem, brick (per-edge `y`-integral).** Integrating the crossing
position over the edge's `y`-range gives `(b.2−a.2)(a.1+b.1)/2`. Proven by FTC
with antiderivative `a.1·y + k·(y−a.2)²/2`. -/
lemma crossThreshold_integral (a b : ℝ × ℝ) (hne : a.2 ≠ b.2) :
    (∫ y in a.2..b.2, crossThreshold a b y) = (b.2 - a.2) * (a.1 + b.1) / 2 := by
  have hd : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hderiv : ∀ y ∈ Set.uIcc a.2 b.2,
      HasDerivAt (fun y => a.1 * y + (b.1 - a.1) / (b.2 - a.2) * ((y - a.2) ^ 2 / 2))
        (crossThreshold a b y) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => a.1 * y) a.1 y := by
      simpa using (hasDerivAt_id y).const_mul a.1
    have hg : HasDerivAt (fun y : ℝ => (y - a.2) ^ 2 / 2) (y - a.2) y := by
      simpa using (((hasDerivAt_id y).sub_const a.2).pow 2).div_const 2
    have h2 := hg.const_mul ((b.1 - a.1) / (b.2 - a.2))
    have hct : crossThreshold a b y = a.1 + (b.1 - a.1) / (b.2 - a.2) * (y - a.2) := by
      simp only [crossThreshold]; ring
    rw [hct]
    exact h1.add h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by simp only [crossThreshold]; fun_prop : Continuous fun y => crossThreshold a b y).intervalIntegrable a.2 b.2)]
  field_simp
  ring

/-- **Green's theorem, brick (threshold contribution).** The difference of two
left-ray indicators `[x<a] − [x<b]` is the indicator of `[b,a)` (for `b ≤ a`), so
its integral is `a − b`. This is the per-threshold contribution to the
cross-section value, handling the per-term divergence via the difference. -/
lemma integral_Iio_indicator_sub (a b : ℝ) (h : b ≤ a) :
    (∫ x, ((Set.Iio a).indicator (fun _ => (1 : ℝ)) x
         - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x)) = a - b := by
  rw [show (fun x => (Set.Iio a).indicator (fun _ => (1 : ℝ)) x
        - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x)
        = (Set.Ico b a).indicator (fun _ => (1 : ℝ)) from ?_]
  · exact integral_indicator_Ico a b h
  · funext x
    simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ico]
    by_cases h1 : x < a <;> by_cases h2 : x < b <;> simp_all <;> linarith

/-- **Green's theorem, brick (threshold integrability).** The cancellation-
adjusted term `[x<a] − [x<b]` is integrable (it equals the indicator of the
bounded interval `[b,a)`), enabling term-by-term integration of the cross-section
sum. -/
lemma integrable_Iio_indicator_sub (a b : ℝ) (h : b ≤ a) :
    MeasureTheory.Integrable (fun x => (Set.Iio a).indicator (fun _ => (1 : ℝ)) x
         - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x) := by
  rw [show (fun x => (Set.Iio a).indicator (fun _ => (1 : ℝ)) x
        - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x)
        = (Set.Ico b a).indicator (fun _ => (1 : ℝ)) from ?_]
  · rw [MeasureTheory.integrable_indicator_iff measurableSet_Ico]
    haveI : Fact (MeasureTheory.volume (Set.Ico b a) < ⊤) := ⟨by
      rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top⟩
    exact MeasureTheory.integrable_const _
  · funext x
    simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ico]
    by_cases h1 : x < a <;> by_cases h2 : x < b <;> simp_all <;> linarith

/-- The real-valued winding as an explicit signed step-function sum (cast of
`winding_generic_sum`). This is the integrand form for the cross-section
integral. -/
lemma winding_real_generic_sum (P : LatticePolygon) (x y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    (P.winding (x, y) : ℝ) = ∑ i,
      (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
          (if x < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y then 1 else 0)
      else 0) := by
  rw [winding_generic_sum P x y hy, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> push_cast <;> ring

/-- **Green's theorem, brick (sign cancellation).** The signed crossing count
`Σ_e sign_e = 0` (at a generic height) — up- and down-crossings balance
(`card_up_eq_card_down`). This is the cancellation enabling term-by-term
integration of the cross-section sum. -/
lemma sum_sign_eq_zero (P : LatticePolygon) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    (∑ i, (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) else 0)) = 0 := by
  classical
  have key : ∀ i,
      (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) else 0)
      = (if (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else 0)
        - (if (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2 then (1 : ℝ) else 0) := by
    intro i
    have ha := hy i
    have hb := hy (i + 1)
    by_cases hup : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2
    · rw [if_pos (Or.inl hup), if_pos hup.2, if_pos ⟨le_of_lt hup.1, hup.2⟩,
        if_neg (fun h => absurd h.2 (not_lt.mpr (le_of_lt hup.1)))]; ring
    · by_cases hdn : (toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2
      · rw [if_pos (Or.inr hdn), if_neg (not_lt.mpr (le_of_lt hdn.1)),
          if_neg (fun h => absurd h.2 (not_lt.mpr (le_of_lt hdn.1))),
          if_pos ⟨le_of_lt hdn.1, hdn.2⟩]; ring
      · rw [if_neg (by tauto),
          if_neg (fun h => hup ⟨lt_of_le_of_ne h.1 ha, h.2⟩),
          if_neg (fun h => hdn ⟨lt_of_le_of_ne h.1 hb, h.2⟩)]; ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib]
  have e : ∀ (p : ZMod P.n → Prop) (_ : DecidablePred p),
      (∑ i, (if p i then (1 : ℝ) else 0)) = ((Finset.univ.filter p).card : ℝ) := by
    intro p _; rw [Finset.card_filter]; push_cast; rfl
  rw [e _ _, e _ _, card_up_eq_card_down]
  ring

/-- General per-threshold integral: `∫([x<a]−[x<b]) = a−b` for **any** `a,b`
(both orders), so the cross-section assembly can use any reference point. -/
lemma integral_Iio_indicator_sub' (a b : ℝ) :
    (∫ x, ((Set.Iio a).indicator (fun _ => (1 : ℝ)) x
         - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x)) = a - b := by
  by_cases h : b ≤ a
  · exact integral_Iio_indicator_sub a b h
  · push_neg at h
    rw [show (fun x => (Set.Iio a).indicator (fun _ => (1 : ℝ)) x
          - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x)
          = (fun x => -((Set.Iio b).indicator (fun _ => (1 : ℝ)) x
            - (Set.Iio a).indicator (fun _ => (1 : ℝ)) x)) from by funext x; ring,
      MeasureTheory.integral_neg, integral_Iio_indicator_sub b a (le_of_lt h)]
    ring

/-- Bridge: the left-ray test `[x < c]` is the indicator of `Iio c`. -/
lemma if_lt_eq_indicator (c x : ℝ) :
    (if x < c then (1 : ℝ) else 0) = (Set.Iio c).indicator (fun _ => 1) x := by
  rw [Set.indicator_apply]
  simp [Set.mem_Iio]

/-- General threshold integrability (any `a,b`): the adjusted indicator term is
integrable regardless of order. -/
lemma integrable_Iio_indicator_sub' (a b : ℝ) :
    MeasureTheory.Integrable (fun x => (Set.Iio a).indicator (fun _ => (1 : ℝ)) x
         - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x) := by
  by_cases h : b ≤ a
  · exact integrable_Iio_indicator_sub a b h
  · push_neg at h
    rw [show (fun x => (Set.Iio a).indicator (fun _ => (1 : ℝ)) x
          - (Set.Iio b).indicator (fun _ => (1 : ℝ)) x)
          = (fun x => -((Set.Iio b).indicator (fun _ => (1 : ℝ)) x
            - (Set.Iio a).indicator (fun _ => (1 : ℝ)) x)) from by funext x; ring]
    exact (integrable_Iio_indicator_sub b a (le_of_lt h)).neg

/-- Per-term integral for the cross-section sum: an adjusted indicator term
integrates to `s·(a−r)` (scaled threshold-difference), or `0` if the edge doesn't
span. -/
lemma integral_adjusted_term (c : Prop) [Decidable c] (s a r : ℝ) :
    (∫ x, (if c then s * ((Set.Iio a).indicator (fun _ => (1 : ℝ)) x
              - (Set.Iio r).indicator (fun _ => (1 : ℝ)) x) else 0))
    = (if c then s * (a - r) else 0) := by
  by_cases hc : c
  · simp only [hc, if_true]
    rw [MeasureTheory.integral_const_mul, integral_Iio_indicator_sub']
  · simp only [hc, if_false, MeasureTheory.integral_zero]

/-- The cast winding equals a sum of **cancellation-adjusted** indicator terms
(reference `0`): subtracting `sign·[x<0]` per edge changes nothing (their sum is
`0` by `sum_sign_eq_zero`), but makes each term integrable. -/
lemma winding_eq_adjusted_sum (P : LatticePolygon) (x y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    (P.winding (x, y) : ℝ) = ∑ i,
      (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
          ((Set.Iio (crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y)).indicator
              (fun _ => (1 : ℝ)) x
            - (Set.Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x)
      else 0) := by
  rw [winding_real_generic_sum P x y hy, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have key : ∀ i,
      ((if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
          (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
            (if x < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y then 1 else 0)
        else 0)
      - (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
          (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
            ((Set.Iio (crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y)).indicator
                (fun _ => (1 : ℝ)) x
              - (Set.Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x)
        else 0))
      = (Set.Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x *
        (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
          (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) else 0) := by
    intro i
    rw [if_lt_eq_indicator]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => key i, ← Finset.mul_sum, sum_sign_eq_zero P y hy, mul_zero]

/-- **Green's theorem — the cross-section value.** `∫_x winding(x,y) dx =
Σ_e sign_e · x*_e` (at a generic height): the inner integral of Fubini equals the
signed sum of crossing positions. -/
theorem crossSection_value (P : LatticePolygon) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    (∫ x, (P.winding (x, y) : ℝ)) = ∑ i,
      (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
          crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y
      else 0) := by
  have hint : ∀ i ∈ (Finset.univ : Finset (ZMod P.n)),
      MeasureTheory.Integrable (fun x =>
        (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
          (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
            ((Set.Iio (crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y)).indicator
                (fun _ => (1 : ℝ)) x
              - (Set.Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x)
        else 0)) := by
    intro i _
    by_cases hsp : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)
    · simp only [hsp, if_true]
      exact (integrable_Iio_indicator_sub' _ _).const_mul _
    · simp only [hsp, if_false]
      exact MeasureTheory.integrable_zero _ _ _
  rw [show (fun x => (P.winding (x, y) : ℝ)) = _ from
    funext fun x => winding_eq_adjusted_sum P x y hy,
    MeasureTheory.integral_finset_sum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_adjusted_term]
  simp only [sub_zero]

/-- Bridge: the full-line integral of an `Ioo`-restricted function equals the
interval integral over that range (`a ≤ b`). Used to evaluate the per-edge
`y`-integral over the edge's `y`-range. -/
lemma integral_Ioo_indicator_eq (f : ℝ → ℝ) (a b : ℝ) (h : a ≤ b) :
    (∫ y, (Set.Ioo a b).indicator f y) = ∫ y in a..b, f y := by
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le h]
  exact (MeasureTheory.integral_Ioc_eq_integral_Ioo).symm

/-- The up-edge cross-section term as an `Ioo`-indicator of `crossThreshold`. -/
lemma edge_term_indicator_up (a b : ℝ × ℝ) (hlt : a.2 < b.2) :
    (fun y => if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0)
      = (Set.Ioo a.2 b.2).indicator (fun y => crossThreshold a b y) := by
  funext y
  by_cases hy : a.2 < y ∧ y < b.2
  · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr hy)]
    have hspan : (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) := Or.inl hy
    rw [if_pos hspan, if_pos hy.2, one_mul]
  · rw [Set.indicator_of_notMem (fun h => hy (Set.mem_Ioo.mp h))]
    have hneg : ¬((a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)) := by
      rintro (h | h)
      · exact hy h
      · linarith [h.1, h.2]
    simp [hneg]

/-- The down-edge cross-section term as an `Ioo`-indicator of `-crossThreshold`. -/
lemma edge_term_indicator_down (a b : ℝ × ℝ) (hgt : b.2 < a.2) :
    (fun y => if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0)
      = (Set.Ioo b.2 a.2).indicator (fun y => -crossThreshold a b y) := by
  funext y
  by_cases hy : b.2 < y ∧ y < a.2
  · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr hy)]
    have hspan : (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) := Or.inr hy
    rw [if_pos hspan, if_neg (not_lt.mpr (le_of_lt hy.1))]; ring
  · rw [Set.indicator_of_notMem (fun h => hy (Set.mem_Ioo.mp h))]
    have hneg : ¬((a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)) := by
      rintro (h | h)
      · linarith [h.1, h.2]
      · exact hy h
    rw [if_neg hneg]

/-- On its (open) spanning interval, an **up-edge**'s cross-section term equals
`crossThreshold` — continuous there. (Within a band avoiding the edge's vertex
heights, the term contributes continuously to `c(y)`.) -/
lemma edge_term_on_Ioo_up (a b : ℝ × ℝ) (hlt : a.2 < b.2) (y : ℝ)
    (hy : y ∈ Set.Ioo a.2 b.2) :
    (if ((a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0) = crossThreshold a b y := by
  have h := congrFun (edge_term_indicator_up a b hlt) y
  rw [h, Set.indicator_of_mem hy]

/-- On its (open) spanning interval, a **down-edge**'s cross-section term equals
`-crossThreshold` — continuous there. -/
lemma edge_term_on_Ioo_down (a b : ℝ × ℝ) (hgt : b.2 < a.2) (y : ℝ)
    (hy : y ∈ Set.Ioo b.2 a.2) :
    (if ((a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2)) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0) = -crossThreshold a b y := by
  have h := congrFun (edge_term_indicator_down a b hgt) y
  rw [h, Set.indicator_of_mem hy]

/-- **Green's theorem, per-edge `y`-integral (up-edge).** For `a.2 < b.2`, the
cross-section term integrated over `y` gives the edge's shoelace contribution
`(b.2−a.2)(a.1+b.1)/2`. -/
lemma edge_y_integral_up (a b : ℝ × ℝ) (hlt : a.2 < b.2) :
    (∫ y, (if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0))
    = (b.2 - a.2) * (a.1 + b.1) / 2 := by
  rw [edge_term_indicator_up a b hlt, integral_Ioo_indicator_eq _ _ _ (le_of_lt hlt),
    crossThreshold_integral a b (ne_of_lt hlt)]

/-- **Per-edge `y`-integral (down-edge).** For `b.2 < a.2`. -/
lemma edge_y_integral_down (a b : ℝ × ℝ) (hgt : b.2 < a.2) :
    (∫ y, (if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0))
    = (b.2 - a.2) * (a.1 + b.1) / 2 := by
  rw [edge_term_indicator_down a b hgt, integral_Ioo_indicator_eq _ _ _ (le_of_lt hgt),
    intervalIntegral.integral_neg,
    intervalIntegral.integral_symm, neg_neg, crossThreshold_integral a b (ne_of_gt hgt)]

/-- **Green's theorem, per-edge `y`-integrability.** Each edge's cross-section
term is integrable in `y` (it is an `Ioo`-indicator of the continuous
`crossThreshold`, supported on a bounded interval). -/
lemma edge_term_y_integrable (a b : ℝ × ℝ) :
    MeasureTheory.Integrable (fun y => if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0) := by
  have hcont : Continuous (fun y => crossThreshold a b y) := by
    simp only [crossThreshold]; fun_prop
  rcases lt_trichotomy a.2 b.2 with hlt | heq | hgt
  · rw [edge_term_indicator_up a b hlt, MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
    exact (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  · rw [show (fun y => if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0) = fun _ => (0 : ℝ) from by
      funext y; rw [if_neg (by rintro (h | h) <;> linarith [h.1, h.2])]]
    exact MeasureTheory.integrable_zero _ _ _
  · rw [edge_term_indicator_down a b hgt, MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
    exact (hcont.neg.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self

/-- **Green's theorem, per-edge `y`-integral.** Integrating the cross-section
contribution of one edge over `y` gives its shoelace contribution
`(b.2−a.2)(a.1+b.1)/2` (all orientations). -/
lemma edge_y_integral (a b : ℝ × ℝ) :
    (∫ y, (if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
        (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0))
    = (b.2 - a.2) * (a.1 + b.1) / 2 := by
  rcases lt_trichotomy a.2 b.2 with hlt | heq | hgt
  · exact edge_y_integral_up a b hlt
  · have hfun : (fun y => if (a.2 < y ∧ y < b.2) ∨ (b.2 < y ∧ y < a.2) then
          (if y < b.2 then (1 : ℝ) else -1) * crossThreshold a b y else 0) = fun _ => (0 : ℝ) := by
      funext y
      rw [if_neg (by rintro (h | h) <;> linarith [h.1, h.2])]
    rw [hfun, MeasureTheory.integral_zero, heq]; ring
  · exact edge_y_integral_down a b hgt

/-- **Green's theorem, telescope to shoelace.** The per-edge `y`-integral
contributions sum to the shoelace: `Σ (b.2−a.2)(a.1+b.1)/2 = shoelace` (the
`cross` terms give `2·shoelace`, the corner products telescope to `0`). -/
lemma sum_edge_contrib_eq_shoelace (P : LatticePolygon) :
    (∑ i, ((toReal (P.vert (i + 1))).2 - (toReal (P.vert i)).2) *
        ((toReal (P.vert i)).1 + (toReal (P.vert (i + 1))).1) / 2) = P.shoelace := by
  have hexp : ∀ i, ((toReal (P.vert (i + 1))).2 - (toReal (P.vert i)).2) *
        ((toReal (P.vert i)).1 + (toReal (P.vert (i + 1))).1) / 2
      = cross (toReal (P.vert i)) (toReal (P.vert (i + 1))) / 2
        + ((toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2
           - (toReal (P.vert i)).1 * (toReal (P.vert i)).2) / 2 := by
    intro i; unfold cross; ring
  have htel : (∑ i, ((toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2
        - (toReal (P.vert i)).1 * (toReal (P.vert i)).2)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have reindex : (∑ i, (toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2)
        = ∑ i, (toReal (P.vert i)).1 * (toReal (P.vert i)).2 :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n))
        (fun i => (toReal (P.vert i)).1 * (toReal (P.vert i)).2)
    rw [reindex, sub_self]
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_div, sum_cross_eq_two_shoelace, htel]
  ring

/-- The vertex heights form a finite set — hence the non-generic heights (where a
vertex sits exactly on the line) are Lebesgue-null. This justifies the a.e.-generic
step in assembling `∫∫ winding = shoelace`. -/
lemma vertexHeights_finite (P : LatticePolygon) :
    {y : ℝ | ∃ i, (toReal (P.vert i)).2 = y}.Finite :=
  Set.finite_range fun i => (toReal (P.vert i)).2

/-- The union of horizontal lines through the vertex heights is Lebesgue-null
(in the plane): a finite set of heights, each line being null. This lets the
a.e. winding-nonnegativity ignore the (null) non-generic heights. -/
lemma vertexHeight_lines_null (P : LatticePolygon) :
    MeasureTheory.volume {q : ℝ × ℝ | ∃ i, (toReal (P.vert i)).2 = q.2} = 0 := by
  have heq : {q : ℝ × ℝ | ∃ i, (toReal (P.vert i)).2 = q.2}
      = Set.univ ×ˢ {y : ℝ | ∃ i, (toReal (P.vert i)).2 = y} := by
    ext ⟨x, y⟩; simp [Set.mem_prod]
  rw [heq, MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod,
    (vertexHeights_finite P).measure_zero]
  simp

/-- **Green's theorem for the lattice polygon.** `∫∫ winding = shoelace`. Assembled
from: `y`-outer Fubini, the cross-section value (a.e. in `y`, off the null
vertex-heights), per-edge `y`-integrability + integral, and the telescope to
shoelace. This is the `hgreen` ingredient of `pick_of_three` — proved here
**Jordan-free** (pure analysis). -/
theorem greens_theorem (P : LatticePolygon) :
    (∫ q, (P.winding q : ℝ)) = P.shoelace := by
  rw [winding_integral_fubini']
  have hae : (fun y => ∫ x, (P.winding (x, y) : ℝ))
      =ᵐ[MeasureTheory.volume] (fun y => ∑ i,
        (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
            ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
          (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
            crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y
        else 0)) := by
    have hco : {y : ℝ | ∀ i, (toReal (P.vert i)).2 ≠ y} ∈ MeasureTheory.ae MeasureTheory.volume := by
      rw [MeasureTheory.mem_ae_iff,
        show {y : ℝ | ∀ i, (toReal (P.vert i)).2 ≠ y}ᶜ
            = {y : ℝ | ∃ i, (toReal (P.vert i)).2 = y} from by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not]]
      exact (vertexHeights_finite P).measure_zero MeasureTheory.volume
    filter_upwards [hco] with y hy
    exact crossSection_value P y hy
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_finset_sum _ fun i _ => edge_term_y_integrable _ _]
  exact (Finset.sum_congr rfl fun i _ =>
      edge_y_integral (toReal (P.vert i)) (toReal (P.vert (i + 1)))).trans
    (sum_edge_contrib_eq_shoelace P)

/-- For a positively-oriented polygon the total winding integral is positive
(`= shoelace > 0` by Green). The "positive average" input to the `winding ≥ 0`
half of the Jordan crux: the cross-section value `t_u − t_d` integrates to
something positive, forcing the (constant) interior sign to be `+1`. -/
lemma winding_integral_pos (P : LatticePolygon) (horient : P.PositivelyOriented) :
    0 < ∫ q, (P.winding q : ℝ) := by
  rw [greens_theorem]; exact horient

/-- The cross-section value is **positive at some height** (for positive
orientation): otherwise it would be `≤ 0` everywhere and integrate to `≤ 0`,
contradicting `∫∫ winding = shoelace > 0`. This supplies the "positive at one
point" hypothesis of the constant-sign engine. -/
lemma crossSection_pos_somewhere (P : LatticePolygon) (horient : P.PositivelyOriented) :
    ∃ y, 0 < ∫ x, (P.winding (x, y) : ℝ) := by
  by_contra h
  push_neg at h
  have hle : (∫ y, ∫ x, (P.winding (x, y) : ℝ)) ≤ 0 := MeasureTheory.integral_nonpos h
  rw [← winding_integral_fubini'] at hle
  exact absurd hle (not_le.mpr (winding_integral_pos P horient))

/-- The cross-section value is positive at some **generic** (non-vertex) height —
the bad set `{c > 0}` would otherwise sit inside the finite vertex heights, leaving
`c ≤ 0` a.e. and `∫∫ winding ≤ 0`. Gives a positive point strictly inside the open
range `(L.2, H.2)` for the engine. -/
lemma crossSection_pos_somewhere_generic (P : LatticePolygon) (horient : P.PositivelyOriented) :
    ∃ y, (∀ i, (toReal (P.vert i)).2 ≠ y) ∧ 0 < ∫ x, (P.winding (x, y) : ℝ) := by
  by_contra h
  push_neg at h
  have hae : ∀ᵐ y ∂MeasureTheory.volume, (∫ x, (P.winding (x, y) : ℝ)) ≤ 0 := by
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ ((vertexHeights_finite P).measure_zero _)
    intro y hy
    rw [Set.mem_setOf_eq] at hy
    by_contra hcon
    rw [Set.mem_setOf_eq] at hcon
    push_neg at hcon
    exact hy (h y hcon)
  have hle : (∫ y, ∫ x, (P.winding (x, y) : ℝ)) ≤ 0 :=
    MeasureTheory.integral_nonpos_of_ae hae
  rw [← winding_integral_fubini'] at hle
  exact absurd hle (not_le.mpr (winding_integral_pos P horient))

/-- **Per-line connection (triangle).** If the cross-section value is positive at
height `y`, then `winding(·,y) ≥ 0` everywhere on that line. Key fact: on a line a
triangle's winding never takes both `+1` and `-1` (the up/down crossing counts are
each antitone in `x`), so a negative value would force `winding ≤ 0` on the whole
line, making `∫ ≤ 0`. -/
lemma winding_nonneg_of_crossSection_pos_triangle (P : LatticePolygon) (hn : P.n = 3) (y : ℝ)
    (hc : 0 < ∫ x, (P.winding (x, y) : ℝ)) :
    ∀ x, 0 ≤ P.winding (x, y) := by
  intro x
  by_contra hneg
  push_neg at hneg
  have hle : ∀ x', P.winding (x', y) ≤ 0 := by
    intro x'
    by_contra h1
    push_neg at h1
    rw [winding_eq_upCount_sub_downCount P x y] at hneg
    rw [winding_eq_upCount_sub_downCount P x' y] at h1
    have hUx := upCount_le_one_triangle P hn x y
    have hDx := downCount_le_one_triangle P hn x y
    have hUx' := upCount_le_one_triangle P hn x' y
    have hDx' := downCount_le_one_triangle P hn x' y
    rcases le_total x x' with hxx | hxx
    · have hanti := upCount_antitone P y x x' hxx
      omega
    · have hanti := downCount_antitone P y x' x hxx
      omega
  have hint : (∫ x, (P.winding (x, y) : ℝ)) ≤ 0 :=
    MeasureTheory.integral_nonpos fun x' => Int.cast_nonpos.mpr (hle x')
  linarith

/-- When the cross-section value is positive, the interior slab is nonempty:
some point on the line has `winding = 1` (else `winding ≡ 0`, giving `∫ = 0`). -/
lemma exists_winding_one_of_crossSection_pos_triangle (P : LatticePolygon) (hn : P.n = 3) (y : ℝ)
    (hc : 0 < ∫ x, (P.winding (x, y) : ℝ)) :
    ∃ x, P.winding (x, y) = 1 := by
  by_contra h
  push_neg at h
  have h0 : ∀ x, P.winding (x, y) = 0 := fun x => by
    have h1 := winding_nonneg_of_crossSection_pos_triangle P hn y hc x
    have h2 := (abs_winding_le_one_triangle P hn x y).2
    have h3 := h x
    omega
  have hz : (∫ x, (P.winding (x, y) : ℝ)) = 0 := by
    have he : (fun x => (P.winding (x, y) : ℝ)) = fun _ => 0 := by
      funext x; rw [h0 x]; simp
    rw [he, MeasureTheory.integral_zero]
  linarith

/-- When `c(y) > 0`, the cross-section value equals the **measure of the interior
slab** `{x | winding (x,y) = 1}` (since `winding ∈ {0,1}` on the line, it is the
indicator of that slab). In particular the slab has positive measure. -/
lemma crossSection_eq_slab_measure_triangle (P : LatticePolygon) (hn : P.n = 3) (y : ℝ)
    (hc : 0 < ∫ x, (P.winding (x, y) : ℝ)) :
    (∫ x, (P.winding (x, y) : ℝ))
      = (MeasureTheory.volume {x : ℝ | P.winding (x, y) = 1}).toReal := by
  have hfun : (fun x => (P.winding (x, y) : ℝ))
      = {x : ℝ | P.winding (x, y) = 1}.indicator (fun _ => (1 : ℝ)) := by
    funext x
    have h1 := winding_nonneg_of_crossSection_pos_triangle P hn y hc x
    have h2 := (abs_winding_le_one_triangle P hn x y).2
    by_cases hx : P.winding (x, y) = 1
    · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | P.winding (x, y) = 1} from hx)]; simp [hx]
    · have h0 : P.winding (x, y) = 0 := by omega
      rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | P.winding (x, y) = 1} from hx)]; simp [h0]
  rw [hfun, MeasureTheory.integral_indicator_const 1 (measurableSet_winding_section_one P y)]
  simp [MeasureTheory.measureReal_def]

/-- The interior slab has **positive measure** when `c(y) > 0`. -/
lemma winding_one_slab_pos_volume_triangle (P : LatticePolygon) (hn : P.n = 3) (y : ℝ)
    (hc : 0 < ∫ x, (P.winding (x, y) : ℝ)) :
    0 < MeasureTheory.volume {x : ℝ | P.winding (x, y) = 1} := by
  rw [crossSection_eq_slab_measure_triangle P hn y hc] at hc
  exact (ENNReal.toReal_pos_iff.mp hc).1

/-- Mirror of the per-line connection: a negative cross-section value forces
`winding(·,y) ≤ 0` on that line. -/
lemma winding_nonpos_of_crossSection_neg_triangle (P : LatticePolygon) (hn : P.n = 3) (y : ℝ)
    (hc : (∫ x, (P.winding (x, y) : ℝ)) < 0) :
    ∀ x, P.winding (x, y) ≤ 0 := by
  intro x
  by_contra hpos
  push_neg at hpos
  have hge : ∀ x', 0 ≤ P.winding (x', y) := by
    intro x'
    by_contra h1
    push_neg at h1
    rw [winding_eq_upCount_sub_downCount P x y] at hpos
    rw [winding_eq_upCount_sub_downCount P x' y] at h1
    have hUx := upCount_le_one_triangle P hn x y
    have hDx := downCount_le_one_triangle P hn x y
    have hUx' := upCount_le_one_triangle P hn x' y
    have hDx' := downCount_le_one_triangle P hn x' y
    rcases le_total x x' with hxx | hxx
    · have hanti := downCount_antitone P y x x' hxx
      omega
    · have hanti := upCount_antitone P y x' x hxx
      omega
  have hf : ∀ x', (0 : ℝ) ≤ (P.winding (x', y) : ℝ) := fun x' => by exact_mod_cast hge x'
  have hint : 0 ≤ (∫ x, (P.winding (x, y) : ℝ)) := MeasureTheory.integral_nonneg hf
  linarith

/-- In `ZMod 3` any two distinct indices are cyclically adjacent. (For a triangle
the two spanning edges are therefore consecutive, so their crossings are distinct
by `crossThreshold_ne_of_simple_adj`.) -/
lemma zmod3_ne_imp_adj : ∀ a b : ZMod 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide

/-- At a generic height the strict spanning filter equals the half-open one, so it
has the cardinality given by `spanning_count_triangle` (`0` or `2`). -/
lemma spanning_filter_strict_eq (P : LatticePolygon) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    = (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)) := by
  apply Finset.filter_congr
  intro i _
  have ha := hy i
  have hb := hy (i + 1)
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨le_of_lt h1, h2⟩
    · exact Or.inr ⟨le_of_lt h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨lt_of_le_of_ne h1 ha, h2⟩
    · exact Or.inr ⟨lt_of_le_of_ne h1 hb, h2⟩

/-- **Distinct spanning edges cross the ray at distinct `x`** (general `n`). Cases
on adjacency: consecutive edges use the shared-vertex clause
(`crossThreshold_ne_of_simple_adj`), non-adjacent ones use disjointness
(`crossThreshold_ne_of_simple'`). -/
lemma crossThreshold_ne_distinct_spanning (P : LatticePolygon) (hP : P.IsSimple) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (a b : ZMod P.n) (hab : a ≠ b)
    (ha : ((toReal (P.vert a)).2 < y ∧ y < (toReal (P.vert (a + 1))).2) ∨
          ((toReal (P.vert (a + 1))).2 < y ∧ y < (toReal (P.vert a)).2))
    (hb : ((toReal (P.vert b)).2 < y ∧ y < (toReal (P.vert (b + 1))).2) ∨
          ((toReal (P.vert (b + 1))).2 < y ∧ y < (toReal (P.vert b)).2)) :
    crossThreshold (toReal (P.vert a)) (toReal (P.vert (a + 1))) y
      ≠ crossThreshold (toReal (P.vert b)) (toReal (P.vert (b + 1))) y := by
  by_cases h1 : a + 1 = b
  · subst h1
    exact crossThreshold_ne_of_simple_adj P hP y a (hy (a + 1)).symm ha hb
  · by_cases h2 : b + 1 = a
    · subst h2
      exact (crossThreshold_ne_of_simple_adj P hP y b (hy (b + 1)).symm hb ha).symm
    · exact crossThreshold_ne_of_simple' P hP y a b hab h1 h2 ha hb

/-- The cross-section value as a sum over **only the spanning edges** (the
non-spanning terms are `0`). For a triangle's 2-spanning height this is a 2-term
sum `t_up − t_down`, nonzero by crossing distinctness — the width-positivity. -/
lemma crossSection_value_filter (P : LatticePolygon) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    (∫ x, (P.winding (x, y) : ℝ)) = ∑ i ∈ Finset.univ.filter (fun i =>
        ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)),
      (if y < (toReal (P.vert (i + 1))).2 then (1 : ℝ) else -1) *
        crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y := by
  rw [crossSection_value P y hy, Finset.sum_filter]

/-- **2-spanning value formula.** When exactly two edges `a, b` span height `y`,
`c(y)` is the signed sum of their two crossings. For a triangle band the two signs
are opposite, so `c(y)` is `±` the gap between the crossings (the slab width); as
`y → M.2` this tends to the non-degenerate gap, giving `c(M.2) ≠ 0`. -/
lemma crossSection_value_two_spanning (P : LatticePolygon) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (a b : ZMod P.n) (hab : a ≠ b)
    (hset : (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)) = {a, b}) :
    (∫ x, (P.winding (x, y) : ℝ))
      = (if y < (toReal (P.vert (a + 1))).2 then (1 : ℝ) else -1) *
          crossThreshold (toReal (P.vert a)) (toReal (P.vert (a + 1))) y
        + (if y < (toReal (P.vert (b + 1))).2 then (1 : ℝ) else -1) *
          crossThreshold (toReal (P.vert b)) (toReal (P.vert (b + 1))) y := by
  rw [crossSection_value_filter P y hy, hset, Finset.sum_pair hab]

/-- Band-1 **genericity**: at a height `y` strictly between the lowest vertex `L`
and both its neighbors, no vertex height equals `y` (the three triangle vertices are
`L` and its two neighbors). -/
lemma band1_generic (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) (y : ℝ)
    (hL : (toReal (P.vert ℓ)).2 < y)
    (hm1 : y < (toReal (P.vert (ℓ - 1))).2)
    (hp1 : y < (toReal (P.vert (ℓ + 1))).2) :
    ∀ i, (toReal (P.vert i)).2 ≠ y := by
  obtain ⟨n, pos, vert⟩ := P
  subst hn
  intro i
  rcases zmod3_neighbor_cases ℓ i with h | h | h
  · subst h; exact ne_of_gt hm1
  · subst h; exact ne_of_lt hL
  · subst h; exact ne_of_gt hp1

/-- Cyclic offset facts in `ZMod P.n` for `P.n = 3`, transported from `ZMod 3` so
the triangle capstone can rewrite neighbor indices without destructuring. -/
lemma zmodPn_add_two_eq_sub_one (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) :
    (ℓ + 1) + 1 = ℓ - 1 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_add_one_add_one ℓ

lemma zmodPn_sub_two_eq_add_one (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) :
    (ℓ - 1) - 1 = ℓ + 1 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_sub_one_sub_one ℓ

/-- A height different from all **three** vertex heights (`vert ℓ` and its two
neighbors) is a non-vertex height — the triangle has only these three. -/
lemma triangle_generic_of_ne_heights (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) (y : ℝ)
    (h1 : (toReal (P.vert ℓ)).2 ≠ y) (h2 : (toReal (P.vert (ℓ - 1))).2 ≠ y)
    (h3 : (toReal (P.vert (ℓ + 1))).2 ≠ y) :
    ∀ i, (toReal (P.vert i)).2 ≠ y := by
  obtain ⟨n, pos, vert⟩ := P
  subst hn
  intro i
  rcases zmod3_neighbor_cases ℓ i with h | h | h
  · subst h; exact h2
  · subst h; exact h1
  · subst h; exact h3

/-- If both neighbors of `ℓ` have height in `{(vert ℓ).2, (vert k).2}`, then every
vertex does (the triangle has only these two heights). -/
lemma triangle_flat_heights (P : LatticePolygon) (hn : P.n = 3) (ℓ k : ZMod P.n)
    (h1 : (toReal (P.vert (ℓ - 1))).2 = (toReal (P.vert ℓ)).2 ∨
          (toReal (P.vert (ℓ - 1))).2 = (toReal (P.vert k)).2)
    (h2 : (toReal (P.vert (ℓ + 1))).2 = (toReal (P.vert ℓ)).2 ∨
          (toReal (P.vert (ℓ + 1))).2 = (toReal (P.vert k)).2) :
    ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert ℓ)).2 ∨
         (toReal (P.vert j)).2 = (toReal (P.vert k)).2 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; intro j
  rcases zmod3_neighbor_cases ℓ j with h | h | h <;> subst h
  · exact h1
  · exact Or.inl rfl
  · exact h2

/-- If all three vertex heights are `≤ (vert k).2`, then `vert k` is highest. -/
lemma triangle_le_max (P : LatticePolygon) (hn : P.n = 3) (ℓ k : ZMod P.n)
    (h1 : (toReal (P.vert ℓ)).2 ≤ (toReal (P.vert k)).2)
    (h2 : (toReal (P.vert (ℓ - 1))).2 ≤ (toReal (P.vert k)).2)
    (h3 : (toReal (P.vert (ℓ + 1))).2 ≤ (toReal (P.vert k)).2) :
    ∀ j, (toReal (P.vert j)).2 ≤ (toReal (P.vert k)).2 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn
  intro j
  rcases zmod3_neighbor_cases ℓ j with h | h | h
  · subst h; exact h2
  · subst h; exact h1
  · subst h; exact h3

/-- **Band-1 spanning edges.** For a triangle, at a height `y` just above the
lowest vertex `L = vert ℓ` and below both its neighbors, the two spanning edges are
exactly those incident to `L`: `{ℓ-1, ℓ}` (the edge into `L` and out of `L`). The
third edge `M–H` lies entirely above `y`. -/
lemma band1_spanning_eq (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) (y : ℝ)
    (hL : (toReal (P.vert ℓ)).2 < y)
    (hm1 : y < (toReal (P.vert (ℓ - 1))).2)
    (hp1 : y < (toReal (P.vert (ℓ + 1))).2) :
    (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)) = {ℓ - 1, ℓ} := by
  obtain ⟨n, pos, vert⟩ := P
  subst hn
  have hy : ∀ i : ZMod 3, (toReal (vert i)).2 ≠ y := by
    intro i
    rcases zmod3_neighbor_cases ℓ i with h | h | h
    · subst h; exact ne_of_gt hm1
    · subst h; exact ne_of_lt hL
    · subst h; exact ne_of_gt hp1
  have hsub : ({ℓ - 1, ℓ} : Finset (ZMod 3)) ⊆ Finset.univ.filter (fun i =>
      ((toReal (vert i)).2 < y ∧ y < (toReal (vert (i + 1))).2) ∨
      ((toReal (vert (i + 1))).2 < y ∧ y < (toReal (vert i)).2)) := by
    intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · subst h
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨?_, hm1⟩⟩
      rw [sub_add_cancel]; exact hL
    · subst h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hL, hp1⟩⟩
  have hcard : (Finset.univ.filter (fun i : ZMod 3 =>
      ((toReal (vert i)).2 < y ∧ y < (toReal (vert (i + 1))).2) ∨
      ((toReal (vert (i + 1))).2 < y ∧ y < (toReal (vert i)).2))).card = 2 := by
    rw [spanning_filter_strict_eq ⟨3, pos, vert⟩ y hy]
    rcases spanning_count_triangle ⟨3, pos, vert⟩ rfl y with h0 | h2
    · exfalso
      have hmem : ℓ ∈ Finset.univ.filter (fun i : ZMod 3 =>
          ((toReal (vert i)).2 ≤ y ∧ y < (toReal (vert (i + 1))).2) ∨
          ((toReal (vert (i + 1))).2 ≤ y ∧ y < (toReal (vert i)).2)) := by
        rw [← spanning_filter_strict_eq ⟨3, pos, vert⟩ y hy]
        exact hsub (show ℓ ∈ ({ℓ - 1, ℓ} : Finset (ZMod 3)) by
          rw [Finset.mem_insert, Finset.mem_singleton]; right; rfl)
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hmem
      exact Finset.notMem_empty _ hmem
    · exact h2
  exact (Finset.eq_of_subset_of_card_le hsub
    (hcard.trans (Finset.card_pair (zmod3_sub_one_ne ℓ)).symm).le).symm

/-- **Band-1 width formula.** With band-1's spanning edges fixed as `{ℓ-1, ℓ}` and
the signs resolved (`ℓ` crosses upward, `ℓ-1` downward), the cross-section value is
the gap between the two crossings: `c(y) = t_ℓ(y) − t_{ℓ-1}(y)`. As `y → M.2` this
gap tends to the non-degenerate `±(M.1 − crossThreshold L H M.2) ≠ 0`. -/
lemma crossSection_band1_eq (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) (y : ℝ)
    (hL : (toReal (P.vert ℓ)).2 < y)
    (hm1 : y < (toReal (P.vert (ℓ - 1))).2)
    (hp1 : y < (toReal (P.vert (ℓ + 1))).2) :
    (∫ x, (P.winding (x, y) : ℝ))
      = crossThreshold (toReal (P.vert ℓ)) (toReal (P.vert (ℓ + 1))) y
        - crossThreshold (toReal (P.vert (ℓ - 1))) (toReal (P.vert ℓ)) y := by
  have hy := band1_generic P hn ℓ y hL hm1 hp1
  have hspan := band1_spanning_eq P hn ℓ y hL hm1 hp1
  have hone : (1 : ZMod P.n) ≠ 0 := by
    haveI : Fact (1 < P.n) := ⟨by rw [hn]; norm_num⟩
    exact one_ne_zero
  have hab : ℓ - 1 ≠ ℓ := fun h => hone (sub_eq_self.mp h)
  rw [crossSection_value_two_spanning P y hy (ℓ - 1) ℓ hab hspan, sub_add_cancel,
    if_neg (not_lt.mpr hL.le), if_pos hp1]
  ring

/-- **Cross-section value at the middle height `m = M.2`.** Passing the band-1 width
formula `c(y) = t_ℓ(y) − t_{ℓ-1}(y)` to the limit `y → m` (both sides continuous at
`m`), the value at the middle vertex height is the crossing gap there. -/
lemma crossSection_at_middle_eq (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n) (m : ℝ)
    (hLm : (toReal (P.vert ℓ)).2 < m)
    (hm1 : m ≤ (toReal (P.vert (ℓ - 1))).2)
    (hp1 : m ≤ (toReal (P.vert (ℓ + 1))).2)
    (hcont : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) m) :
    (∫ x, (P.winding (x, m) : ℝ))
      = crossThreshold (toReal (P.vert ℓ)) (toReal (P.vert (ℓ + 1))) m
        - crossThreshold (toReal (P.vert (ℓ - 1))) (toReal (P.vert ℓ)) m := by
  refine eq_of_continuousAt_eqOn_left (fun y => ∫ x, (P.winding (x, y) : ℝ))
    (fun y => crossThreshold (toReal (P.vert ℓ)) (toReal (P.vert (ℓ + 1))) y
        - crossThreshold (toReal (P.vert (ℓ - 1))) (toReal (P.vert ℓ)) y)
    (toReal (P.vert ℓ)).2 m hLm hcont ?_ ?_
  · exact (Continuous.sub (crossThreshold_continuous _ _) (crossThreshold_continuous _ _)).continuousAt
  · intro y hy
    exact crossSection_band1_eq P hn ℓ y hy.1 (lt_of_lt_of_le hy.2 hm1) (lt_of_lt_of_le hy.2 hp1)

/-- Case **`M` is `L`'s upper neighbor** (`M = vert (ℓ+1)`, at height `m = M.2`):
the `L→M` crossing collapses to `M.1` (`crossThreshold_top`), so
`c(M.2) = M.1 − crossThreshold(H, L, M.2)`. -/
lemma crossSection_at_upper_neighbor (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n)
    (hLm : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ + 1))).2)
    (hH : (toReal (P.vert (ℓ + 1))).2 ≤ (toReal (P.vert (ℓ - 1))).2)
    (hcont : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) (toReal (P.vert (ℓ + 1))).2) :
    (∫ x, (P.winding (x, (toReal (P.vert (ℓ + 1))).2) : ℝ))
      = (toReal (P.vert (ℓ + 1))).1
        - crossThreshold (toReal (P.vert (ℓ - 1))) (toReal (P.vert ℓ))
            (toReal (P.vert (ℓ + 1))).2 := by
  rw [crossSection_at_middle_eq P hn ℓ (toReal (P.vert (ℓ + 1))).2 hLm hH le_rfl hcont,
    crossThreshold_top (toReal (P.vert ℓ)) (toReal (P.vert (ℓ + 1))) (ne_of_lt hLm)]

/-- Case **`M` is `L`'s lower neighbor** (`M = vert (ℓ-1)`, at height `m = M.2`):
the `M→L` crossing collapses to `M.1` (`crossThreshold_bot`), so
`c(M.2) = crossThreshold(L, H, M.2) − M.1`. -/
lemma crossSection_at_lower_neighbor (P : LatticePolygon) (hn : P.n = 3) (ℓ : ZMod P.n)
    (hLm : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ - 1))).2)
    (hH : (toReal (P.vert (ℓ - 1))).2 ≤ (toReal (P.vert (ℓ + 1))).2)
    (hcont : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) (toReal (P.vert (ℓ - 1))).2) :
    (∫ x, (P.winding (x, (toReal (P.vert (ℓ - 1))).2) : ℝ))
      = crossThreshold (toReal (P.vert ℓ)) (toReal (P.vert (ℓ + 1)))
            (toReal (P.vert (ℓ - 1))).2
        - (toReal (P.vert (ℓ - 1))).1 := by
  rw [crossSection_at_middle_eq P hn ℓ (toReal (P.vert (ℓ - 1))).2 hLm le_rfl hH hcont,
    crossThreshold_bot (toReal (P.vert (ℓ - 1))) (toReal (P.vert ℓ))]

/-- **`c(M.2) ≠ 0`, upper-neighbor case.** The value `M.1 − crossThreshold(H,L,M.2)`
is nonzero because `M` is non-collinear with `L, H` (`corner_cross_base_pos`), so the
`L–H` crossing misses `M.1`. -/
lemma crossSection_at_upper_neighbor_ne_zero (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (ℓ : ZMod P.n)
    (hLm : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ + 1))).2)
    (hH : (toReal (P.vert (ℓ + 1))).2 ≤ (toReal (P.vert (ℓ - 1))).2)
    (hcont : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) (toReal (P.vert (ℓ + 1))).2) :
    (∫ x, (P.winding (x, (toReal (P.vert (ℓ + 1))).2) : ℝ)) ≠ 0 := by
  rw [crossSection_at_upper_neighbor P hn ℓ hLm hH hcont, sub_ne_zero]
  exact (crossThreshold_ne_of_cross_ne_zero (toReal (P.vert (ℓ - 1))) (toReal (P.vert ℓ))
    (toReal (P.vert (ℓ + 1))) (ne_of_gt (lt_of_lt_of_le hLm hH))
    (ne_of_gt (corner_cross_base_pos P hn horient ℓ))).symm

/-- **`c(M.2) ≠ 0`, lower-neighbor case** (symmetric; the same non-degeneracy is
reused via `cross_corner_cycle`). -/
lemma crossSection_at_lower_neighbor_ne_zero (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (ℓ : ZMod P.n)
    (hLm : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ - 1))).2)
    (hH : (toReal (P.vert (ℓ - 1))).2 ≤ (toReal (P.vert (ℓ + 1))).2)
    (hcont : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) (toReal (P.vert (ℓ - 1))).2) :
    (∫ x, (P.winding (x, (toReal (P.vert (ℓ - 1))).2) : ℝ)) ≠ 0 := by
  rw [crossSection_at_lower_neighbor P hn ℓ hLm hH hcont, sub_ne_zero]
  refine crossThreshold_ne_of_cross_ne_zero (toReal (P.vert ℓ)) (toReal (P.vert (ℓ + 1)))
    (toReal (P.vert (ℓ - 1))) (ne_of_lt (lt_of_lt_of_le hLm hH)) ?_
  rw [cross_corner_cycle (toReal (P.vert (ℓ - 1))) (toReal (P.vert ℓ)) (toReal (P.vert (ℓ + 1)))]
  exact ne_of_gt (corner_cross_base_pos P hn horient ℓ)

/-- **Width-positivity (triangle).** At a 2-spanning generic height the
cross-section value is nonzero: it equals `t_up − t_down` (the two crossing
positions, distinct by simplicity), the sign pairing `sgn_a + sgn_b = 0` coming
for free from `sum_sign_eq_zero`. -/
lemma crossSection_ne_zero_triangle (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (hsp : (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0) :
    (∫ x, (P.winding (x, y) : ℝ)) ≠ 0 := by
  have hcard : (Finset.univ.filter fun i =>
      ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)).card = 2 := by
    rw [spanning_filter_strict_eq P y hy]
    rcases spanning_count_triangle P hn y with h | h
    · exact absurd h hsp
    · exact h
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  have ha := (Finset.mem_filter.mp (hset ▸ Finset.mem_insert_self a {b})).2
  have hb := (Finset.mem_filter.mp (hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))).2
  have hne := crossThreshold_ne_distinct_spanning P hP y hy a b hab ha hb
  have hsgn : (if y < (toReal (P.vert (a + 1))).2 then (1 : ℝ) else -1)
      + (if y < (toReal (P.vert (b + 1))).2 then (1 : ℝ) else -1) = 0 := by
    have h := sum_sign_eq_zero P y hy
    rw [← Finset.sum_filter, hset, Finset.sum_pair hab] at h
    exact h
  rw [crossSection_value_filter P y hy, hset, Finset.sum_pair hab]
  intro hc
  split_ifs at hsgn hc <;> exact hne (by linarith)

/-- **Converse direction.** If `winding = 1` at some point of the line and the
cross-section value is nonzero, then it is positive (a negative value would force
`winding ≤ 0` there by the mirror per-line). This propagates positivity across the
middle vertex: a `winding=1` point near `M.2` (carried over from a positive band)
makes the cross-section positive on the other band. -/
lemma crossSection_pos_of_winding_one_triangle (P : LatticePolygon) (hn : P.n = 3) (y : ℝ)
    (x₀ : ℝ) (hw : P.winding (x₀, y) = 1) (hne : (∫ x, (P.winding (x, y) : ℝ)) ≠ 0) :
    0 < ∫ x, (P.winding (x, y) : ℝ) := by
  rcases lt_trichotomy (∫ x, (P.winding (x, y) : ℝ)) 0 with h | h | h
  · have hle := winding_nonpos_of_crossSection_neg_triangle P hn y h x₀
    omega
  · exact absurd h hne
  · exact h

/-- **Triangle `winding ≥ 0` reduces to cross-section positivity.** If the
cross-section value is positive at every spanning height, the winding is `≥ 0`
everywhere (non-spanning heights give `winding = 0`). Combined with
`h01_triangle_of_nonneg`, this reduces triangle `h01` to: `c(y) > 0` on the
spanning range — to be supplied by the constant-sign engine + width-positivity. -/
lemma winding_nonneg_triangle_of_crossSection_pos (P : LatticePolygon) (hn : P.n = 3)
    (hpos : ∀ y, (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 →
        0 < ∫ x, (P.winding (x, y) : ℝ)) :
    ∀ q : ℝ × ℝ, 0 ≤ P.winding q := by
  rintro ⟨x, y⟩
  by_cases hsp : (Finset.univ.filter fun i =>
      ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card = 0
  · rw [winding_zero_of_no_spanning P x y hsp]
  · exact winding_nonneg_of_crossSection_pos_triangle P hn y (hpos y hsp) x

/-- **a.e. version of the reduction.** It suffices to have `c(y) > 0` at every
*generic* spanning height (no vertex at `y`); the non-generic heights form null
lines, so `winding ≥ 0` holds a.e. (which is all `area = ∫∫ winding` needs). -/
lemma winding_nonneg_ae_triangle_of_crossSection_pos (P : LatticePolygon) (hn : P.n = 3)
    (hpos : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
        (Finset.univ.filter fun i =>
          ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 →
        0 < ∫ x, (P.winding (x, y) : ℝ)) :
    ∀ᵐ q ∂MeasureTheory.volume, 0 ≤ P.winding q := by
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null _ (vertexHeight_lines_null P)
  rintro ⟨x, y⟩ hq
  rw [Set.mem_setOf_eq] at hq
  by_contra hc
  rw [Set.mem_setOf_eq] at hc
  push_neg at hc
  refine hq ?_
  by_cases hsp : (Finset.univ.filter fun i =>
      ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card = 0
  · exact le_of_eq (winding_zero_of_no_spanning P x y hsp).symm
  · exact winding_nonneg_of_crossSection_pos_triangle P hn y (hpos y hc hsp) x

/-- The constant-sign engine specialized to the cross-section value: on an open
height-interval where `c` is continuous, nonvanishing, and positive somewhere,
`c > 0` throughout. (Applied to a band of the spanning range.) -/
lemma crossSection_pos_on_Ioo (P : LatticePolygon) (a b : ℝ)
    (hcont : ContinuousOn (fun y => ∫ x, (P.winding (x, y) : ℝ)) (Set.Ioo a b))
    (hne : ∀ y ∈ Set.Ioo a b, (∫ x, (P.winding (x, y) : ℝ)) ≠ 0)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Set.Ioo a b) (hpos : 0 < ∫ x, (P.winding (x, y₀) : ℝ))
    (y : ℝ) (hy : y ∈ Set.Ioo a b) : 0 < ∫ x, (P.winding (x, y) : ℝ) :=
  pos_of_continuousOn_ne_zero_Ioo (fun y => ∫ x, (P.winding (x, y) : ℝ)) a b hcont hne y₀ hy₀ hpos y hy

/-- Real-valued uniform bound on the winding: `|winding q| ≤ n`. Combined with the
bounded support, this dominates the cross-section integrand for the
dominated-convergence continuity of `c(y)`. -/
lemma abs_winding_real_le (P : LatticePolygon) (q : ℝ × ℝ) :
    |(P.winding q : ℝ)| ≤ (P.n : ℝ) := by
  rw [← Int.cast_abs]
  exact_mod_cast abs_winding_le P q

/-- The winding vanishes for `|x|` large, **uniformly in `y`** (the support is
bounded). Gives the bounded `x`-support for the dominated-convergence continuity
of the cross-section value. -/
lemma exists_winding_zero_far_x (P : LatticePolygon) :
    ∃ R : ℝ, ∀ x y, R < |x| → P.winding (x, y) = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp (windingSupport_bounded P)
  refine ⟨R, fun x y hx => ?_⟩
  by_contra hne
  have hmem : (x, y) ∈ {q : ℝ × ℝ | P.winding q ≠ 0} := hne
  have hball := hR hmem
  rw [Metric.mem_closedBall, Prod.dist_eq] at hball
  simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right, Real.norm_eq_abs] at hball
  have : |x| ≤ R := le_trans (le_max_left _ _) hball
  linarith

/-- An **integrable dominator** for the cross-section integrand, uniform in `y`:
`|winding(x,y)| ≤ n · 𝟙[-R,R](x)` with the right side integrable. This is the
domination hypothesis of `continuousAt_of_dominated` for proving `c(y)` continuous. -/
lemma winding_section_dominated (P : LatticePolygon) :
    ∃ R : ℝ, MeasureTheory.Integrable
        (fun x => (P.n : ℝ) * (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ)) x) ∧
      ∀ x y, |(P.winding (x, y) : ℝ)|
        ≤ (P.n : ℝ) * (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ)) x := by
  obtain ⟨R, hR⟩ := exists_winding_zero_far_x P
  refine ⟨R, MeasureTheory.Integrable.const_mul ?_ _, fun x y => ?_⟩
  · rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    haveI : Fact (MeasureTheory.volume (Set.Icc (-R) R) < ⊤) :=
      ⟨by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    exact MeasureTheory.integrable_const _
  · by_cases hx : |x| ≤ R
    · rw [abs_le] at hx
      rw [Set.indicator_of_mem (Set.mem_Icc.mpr hx), mul_one]
      exact abs_winding_real_le P (x, y)
    · push_neg at hx
      rw [hR x y hx,
        Set.indicator_of_notMem (fun h => absurd (abs_le.mpr (Set.mem_Icc.mp h)) (not_le.mpr hx))]
      simp

/-- **Cross-section value continuity, modulo the one fundamental gap.** Given the
a.e.-continuity of the sections `winding(x,·)` at `y₀` (the vertical local
constancy of the winding number — the deep frontier), `c(y) = ∫_x winding(x,y) dx`
is continuous at `y₀`. Assembled via `continuousAt_of_dominated` from the section
measurability and the integrable dominator (both in hand). -/
lemma crossSection_continuousAt (P : LatticePolygon) (y₀ : ℝ)
    (hcont : ∀ᵐ x ∂MeasureTheory.volume,
      ContinuousAt (fun y => (P.winding (x, y) : ℝ)) y₀) :
    ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) y₀ := by
  obtain ⟨R, hint, hbound⟩ := winding_section_dominated P
  refine MeasureTheory.continuousAt_of_dominated
    (Filter.Eventually.of_forall fun y => (measurable_crossSection P y).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => MeasureTheory.ae_of_all _ fun x => ?_)
    hint hcont
  rw [Real.norm_eq_abs]; exact hbound x y

/-- **Cross-section value continuous at non-vertex heights.** Unconditional
(no extra hypotheses beyond `y₀` not being a vertex height): the a.e.-continuity
holds automatically there. So `c(y) = ∫_x winding(x,y) dx` is continuous off the
finite set of vertex heights — in particular on each open band of the spanning
range. -/
lemma crossSection_continuousAt_of_not_vertex (P : LatticePolygon) (y₀ : ℝ)
    (hv : ∀ i, y₀ ≠ (toReal (P.vert i)).2) :
    ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) y₀ :=
  crossSection_continuousAt P y₀ (winding_section_ae_continuousAt_of_not_vertex P y₀ hv)

/-- `c(y) = ∫_x winding(x,y) dx` is continuous **on** any set avoiding all vertex
heights — in particular on each open band of the spanning range. -/
lemma crossSection_continuousOn (P : LatticePolygon) (s : Set ℝ)
    (hs : ∀ y ∈ s, ∀ i, y ≠ (toReal (P.vert i)).2) :
    ContinuousOn (fun y => ∫ x, (P.winding (x, y) : ℝ)) s :=
  fun y hy => (crossSection_continuousAt_of_not_vertex P y (hs y hy)).continuousWithinAt

/-- **Band-assembly.** On an open height-band avoiding all vertex heights and
everywhere spanning, the cross-section value is positive throughout once positive
at one point (continuity + width-positivity + the engine). -/
lemma crossSection_pos_on_band (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3) (a b : ℝ)
    (hgen : ∀ y ∈ Set.Ioo a b, ∀ i, (toReal (P.vert i)).2 ≠ y)
    (hsp : ∀ y ∈ Set.Ioo a b, (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Set.Ioo a b) (hpos : 0 < ∫ x, (P.winding (x, y₀) : ℝ))
    (y : ℝ) (hy : y ∈ Set.Ioo a b) : 0 < ∫ x, (P.winding (x, y) : ℝ) :=
  crossSection_pos_on_Ioo P a b (crossSection_continuousOn P _ fun y hy i => (hgen y hy i).symm)
    (fun y hy => crossSection_ne_zero_triangle P hP hn y (hgen y hy) (hsp y hy)) y₀ hy₀ hpos y hy

/-- `c(y)` is continuous at a **pass-through vertex height** (combining the a.e.
section continuity there with the dominated-convergence engine). Together with
`crossSection_continuousAt_of_not_vertex`, this covers every interior point of a
triangle's spanning range (whose only interior vertex is the pass-through `M`). -/
lemma crossSection_continuousAt_passthrough (P : LatticePolygon) (k : ZMod P.n)
    (hk : k - 1 ≠ k)
    (hpass : ((toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k + 1))).2) ∨
             ((toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k - 1))).2))
    (hdist : ∀ i ∈ (Finset.univ.erase (k - 1)).erase k,
        (toReal (P.vert k)).2 ≠ (toReal (P.vert i)).2 ∧
        (toReal (P.vert k)).2 ≠ (toReal (P.vert (i + 1))).2) :
    ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) (toReal (P.vert k)).2 :=
  crossSection_continuousAt P _ (winding_section_ae_continuousAt_passthrough P k hk hpass hdist)

/-- **`c` is continuous at the middle vertex height** of a triangle: `M = vert k`
has its two cyclic neighbors straddling `M.2` (a pass-through), so the only nonzero
hypotheses of `crossSection_continuousAt_passthrough` reduce to `M.2 ≠` the two
neighbor heights — immediate from the straddle. -/
lemma crossSection_continuousAt_middle (P : LatticePolygon) (hn : P.n = 3) (k : ZMod P.n)
    (hpass : ((toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k + 1))).2) ∨
             ((toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2 ∧
              (toReal (P.vert k)).2 < (toReal (P.vert (k - 1))).2)) :
    ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) (toReal (P.vert k)).2 := by
  obtain ⟨n, pos, vert⟩ := P
  subst hn
  refine crossSection_continuousAt_passthrough ⟨3, pos, vert⟩ k (zmod3_sub_one_ne k) hpass ?_
  intro i hi
  rw [zmod3_erase_two k, Finset.mem_singleton] at hi
  subst hi
  refine ⟨?_, ?_⟩
  · rcases hpass with ⟨_, h⟩ | ⟨h, _⟩
    · exact ne_of_lt h
    · exact ne_of_gt h
  · rw [zmod3_add_one_add_one k]
    rcases hpass with ⟨h, _⟩ | ⟨_, h⟩
    · exact ne_of_gt h
    · exact ne_of_lt h

/-- **`c` is continuous on the spanning range `(a, b)`** given continuity at the one
interior vertex height `m` and the fact that every other in-range height is a
non-vertex. (For a triangle `m = M.2` is the sole interior vertex height.) -/
lemma crossSection_continuousOn_of_middle (P : LatticePolygon) (a b m : ℝ)
    (hcont_m : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ)) m)
    (hgen : ∀ y ∈ Set.Ioo a b, y ≠ m → ∀ i, (toReal (P.vert i)).2 ≠ y) :
    ContinuousOn (fun y => ∫ x, (P.winding (x, y) : ℝ)) (Set.Ioo a b) := by
  intro y hy
  by_cases hym : y = m
  · subst hym; exact hcont_m.continuousWithinAt
  · exact (crossSection_continuousAt_of_not_vertex P y
      (fun i => (hgen y hy hym i).symm)).continuousWithinAt

/-- **`c ≠ 0` on the spanning range `(a, b)`** given `c(m) ≠ 0` (the cross-band) and,
for every other in-range height, genericity + spanning (so width-positivity applies).
This is the key use of the cross-band: it extends `c ≠ 0` across the interior vertex
line, making `c` nonvanishing on the whole connected range. -/
lemma crossSection_ne_zero_on_range (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (a b m : ℝ) (hne_m : (∫ x, (P.winding (x, m) : ℝ)) ≠ 0)
    (hgen : ∀ y ∈ Set.Ioo a b, y ≠ m → ∀ i, (toReal (P.vert i)).2 ≠ y)
    (hsp : ∀ y ∈ Set.Ioo a b, y ≠ m → (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0) :
    ∀ y ∈ Set.Ioo a b, (∫ x, (P.winding (x, y) : ℝ)) ≠ 0 := by
  intro y hy
  by_cases hym : y = m
  · subst hym; exact hne_m
  · exact crossSection_ne_zero_triangle P hP hn y (hgen y hy hym) (hsp y hy hym)

/-- A **generic spanning** height lies in the open range `(L.2, H.2)` (`L` lowest,
`H` highest): a spanning edge brackets `y` between vertex heights, all `≥ L.2` and
`≤ H.2`, and genericity makes the lower bound strict. -/
lemma spanning_mem_range (P : LatticePolygon) (ℓ hh : ZMod P.n)
    (hL : ∀ j, (toReal (P.vert ℓ)).2 ≤ (toReal (P.vert j)).2)
    (hH : ∀ j, (toReal (P.vert j)).2 ≤ (toReal (P.vert hh)).2)
    (y : ℝ) (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (hsp : (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0) :
    (toReal (P.vert ℓ)).2 < y ∧ y < (toReal (P.vert hh)).2 := by
  obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp hsp
  rw [Finset.mem_filter] at hi
  obtain ⟨_, hi⟩ := hi
  refine ⟨?_, ?_⟩
  · rcases hi with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_le_of_ne (le_trans (hL i) h1) (hgen ℓ)
    · exact lt_of_le_of_ne (le_trans (hL (i + 1)) h1) (hgen ℓ)
  · rcases hi with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact lt_of_lt_of_le h2 (hH (i + 1))
    · exact lt_of_lt_of_le h2 (hH i)

/-- The cross-section value vanishes at a height crossed by no edge (the whole
section is `0`). So `c(y) = 0` below the lowest and above the highest vertex —
the endpoints of the spanning range. -/
lemma crossSection_eq_zero_of_no_spanning (P : LatticePolygon) (y : ℝ)
    (hsp : (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card = 0) :
    (∫ x, (P.winding (x, y) : ℝ)) = 0 := by
  have hz : (fun x => (P.winding (x, y) : ℝ)) = fun _ => 0 := by
    funext x; rw [winding_zero_of_no_spanning P x y hsp]; simp
  rw [hz, MeasureTheory.integral_zero]

/-- Contrapositive: a **nonzero** cross-section value forces a spanning edge at `y`.
So any height where `c ≠ 0` (in particular `c > 0`) lies in the spanning range —
used to place the initial positive point `y₀` inside `(L.2, H.2)`. -/
lemma spanning_of_crossSection_ne_zero (P : LatticePolygon) (y : ℝ)
    (hc : (∫ x, (P.winding (x, y) : ℝ)) ≠ 0) :
    (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 :=
  fun h => hc (crossSection_eq_zero_of_no_spanning P y h)

/-- The interior region as a preimage of `{1}` under the winding map. -/
lemma interiorRegion_eq_preimage (P : LatticePolygon) :
    P.interiorRegion = P.winding ⁻¹' {1} := rfl

/-- Every winding level set is measurable — the winding map is measurable. Toward
the area decomposition `∫∫ winding = Σ k · vol(winding⁻¹{k})`. -/
lemma measurableSet_winding_preimage (P : LatticePolygon) (k : ℤ) :
    MeasurableSet (P.winding ⁻¹' {k}) :=
  measurable_winding P (measurableSet_singleton k)

/-- The winding takes values in the finite range `[-n, n]`: combined with finite
support, only finitely many levels are nonempty, so the area decomposition is a
finite sum. -/
lemma winding_mem_Icc (P : LatticePolygon) (q : ℝ × ℝ) :
    P.winding q ∈ Finset.Icc (-(P.n : ℤ)) (P.n : ℤ) := by
  rw [Finset.mem_Icc, ← abs_le]
  exact abs_winding_le P q

/-- The interior region lies (weakly) above the lowest vertex: below the lowest
vertex the winding is `0`, so no interior points are there. Bounds the interior's
`y`-extent below. -/
lemma interiorRegion_above_lowest (P : LatticePolygon) :
    ∃ m : ZMod P.n, ∀ q ∈ P.interiorRegion, (toReal (P.vert m)).2 ≤ q.2 := by
  obtain ⟨m, hm⟩ := exists_lowest_vertex P
  refine ⟨m, fun q hq => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hw : P.winding q = 0 := by
    have h := winding_zero_of_y_below P q.1 q.2 (fun j => lt_of_lt_of_le hlt (hm j))
    rwa [Prod.mk.eta] at h
  simp only [LatticePolygon.interiorRegion, Set.mem_setOf_eq] at hq
  rw [hw] at hq
  exact absurd hq (by norm_num)

/-- The corner turn is an integer (cast): each corner triangle of a lattice
polygon has half-integer area. -/
lemma turn_int (P : LatticePolygon) (i : ZMod P.n) :
    cross (toReal (P.vert i) - toReal (P.vert (i - 1)))
        (toReal (P.vert (i + 1)) - toReal (P.vert i)) =
      ((((P.vert (i - 1)).1 * (P.vert i).2 - (P.vert (i - 1)).2 * (P.vert i).1) +
        ((P.vert i).1 * (P.vert (i + 1)).2 - (P.vert i).2 * (P.vert (i + 1)).1) +
        ((P.vert (i + 1)).1 * (P.vert (i - 1)).2 - (P.vert (i + 1)).2 * (P.vert (i - 1)).1) : ℤ) : ℝ) := by
  rw [turn_eq_cornerArea, cross_toReal_int, cross_toReal_int, cross_toReal_int]
  push_cast
  ring

/-- **Triangle `hpos`, 3-distinct upper-neighbor case.** With `L = vert ℓ` lowest,
its upper neighbor `M = vert (ℓ+1)` the strict middle, and `H = vert (ℓ-1)` highest,
`c > 0` at every generic spanning height: `c` is continuous and nonvanishing on the
whole connected range `(L.2, H.2)` (cross-band at `M.2`, width elsewhere) and
positive somewhere, so the constant-sign engine gives `c > 0` throughout. -/
lemma triangle_hpos_upper_strict (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (ℓ : ZMod P.n)
    (hL : ∀ j, (toReal (P.vert ℓ)).2 ≤ (toReal (P.vert j)).2)
    (h_lm : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ + 1))).2)
    (h_mh : (toReal (P.vert (ℓ + 1))).2 < (toReal (P.vert (ℓ - 1))).2) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 →
      0 < ∫ x, (P.winding (x, y) : ℝ) := by
  have hH : ∀ j, (toReal (P.vert j)).2 ≤ (toReal (P.vert (ℓ - 1))).2 :=
    triangle_le_max P hn ℓ (ℓ - 1) (h_lm.le.trans h_mh.le) le_rfl h_mh.le
  have hcont_m : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ))
      (toReal (P.vert (ℓ + 1))).2 := by
    apply crossSection_continuousAt_middle P hn (ℓ + 1)
    refine Or.inl ⟨?_, ?_⟩
    · rw [show (ℓ + 1) - 1 = ℓ from by ring]; exact h_lm
    · rw [zmodPn_add_two_eq_sub_one P hn ℓ]; exact h_mh
  have hne_m : (∫ x, (P.winding (x, (toReal (P.vert (ℓ + 1))).2) : ℝ)) ≠ 0 :=
    crossSection_at_upper_neighbor_ne_zero P hn horient ℓ h_lm h_mh.le hcont_m
  have hgen' : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2,
      y' ≠ (toReal (P.vert (ℓ + 1))).2 → ∀ i, (toReal (P.vert i)).2 ≠ y' :=
    fun y' hy' hy'm => triangle_generic_of_ne_heights P hn ℓ y'
      (ne_of_lt hy'.1) (ne_of_gt hy'.2) (Ne.symm hy'm)
  have hsp' : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2,
      y' ≠ (toReal (P.vert (ℓ + 1))).2 → (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y' ∧ y' < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y' ∧ y' < (toReal (P.vert i)).2)).card ≠ 0 := by
    intro y' hy' _
    refine Finset.card_ne_zero.mpr ⟨ℓ - 1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨?_, hy'.2⟩⟩⟩
    rw [sub_add_cancel]; exact hy'.1.le
  have hcont : ContinuousOn (fun y => ∫ x, (P.winding (x, y) : ℝ))
      (Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2) :=
    crossSection_continuousOn_of_middle P _ _ (toReal (P.vert (ℓ + 1))).2 hcont_m hgen'
  have hne : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2,
      (∫ x, (P.winding (x, y') : ℝ)) ≠ 0 :=
    crossSection_ne_zero_on_range P hP hn _ _ _ hne_m hgen' hsp'
  obtain ⟨y₀, hy₀gen, hy₀pos⟩ := crossSection_pos_somewhere_generic P horient
  obtain ⟨hy₀1, hy₀2⟩ := spanning_mem_range P ℓ (ℓ - 1) hL hH y₀ hy₀gen
    (spanning_of_crossSection_ne_zero P y₀ (ne_of_gt hy₀pos))
  intro y hgen hsp
  obtain ⟨hy1, hy2⟩ := spanning_mem_range P ℓ (ℓ - 1) hL hH y hgen hsp
  exact crossSection_pos_on_Ioo P _ _ hcont hne y₀ ⟨hy₀1, hy₀2⟩ hy₀pos y ⟨hy1, hy2⟩

/-- **Triangle `hpos`, 3-distinct lower-neighbor case** (mirror of
`triangle_hpos_upper_strict`: the strict middle `M = vert (ℓ-1)` is `L`'s lower
neighbor, `H = vert (ℓ+1)` highest). -/
lemma triangle_hpos_lower_strict (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (ℓ : ZMod P.n)
    (hL : ∀ j, (toReal (P.vert ℓ)).2 ≤ (toReal (P.vert j)).2)
    (h_lm : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ - 1))).2)
    (h_mh : (toReal (P.vert (ℓ - 1))).2 < (toReal (P.vert (ℓ + 1))).2) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 →
      0 < ∫ x, (P.winding (x, y) : ℝ) := by
  have hH : ∀ j, (toReal (P.vert j)).2 ≤ (toReal (P.vert (ℓ + 1))).2 :=
    triangle_le_max P hn ℓ (ℓ + 1) (h_lm.trans h_mh).le h_mh.le le_rfl
  have hcont_m : ContinuousAt (fun y => ∫ x, (P.winding (x, y) : ℝ))
      (toReal (P.vert (ℓ - 1))).2 := by
    apply crossSection_continuousAt_middle P hn (ℓ - 1)
    refine Or.inr ⟨?_, ?_⟩
    · rw [show (ℓ - 1) + 1 = ℓ from by ring]; exact h_lm
    · rw [zmodPn_sub_two_eq_add_one P hn ℓ]; exact h_mh
  have hne_m : (∫ x, (P.winding (x, (toReal (P.vert (ℓ - 1))).2) : ℝ)) ≠ 0 :=
    crossSection_at_lower_neighbor_ne_zero P hn horient ℓ h_lm h_mh.le hcont_m
  have hgen' : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2,
      y' ≠ (toReal (P.vert (ℓ - 1))).2 → ∀ i, (toReal (P.vert i)).2 ≠ y' :=
    fun y' hy' hy'm => triangle_generic_of_ne_heights P hn ℓ y'
      (ne_of_lt hy'.1) (Ne.symm hy'm) (ne_of_gt hy'.2)
  have hsp' : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2,
      y' ≠ (toReal (P.vert (ℓ - 1))).2 → (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y' ∧ y' < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y' ∧ y' < (toReal (P.vert i)).2)).card ≠ 0 := by
    intro y' hy' _
    exact Finset.card_ne_zero.mpr ⟨ℓ,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hy'.1.le, hy'.2⟩⟩⟩
  have hcont : ContinuousOn (fun y => ∫ x, (P.winding (x, y) : ℝ))
      (Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2) :=
    crossSection_continuousOn_of_middle P _ _ (toReal (P.vert (ℓ - 1))).2 hcont_m hgen'
  have hne : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2,
      (∫ x, (P.winding (x, y') : ℝ)) ≠ 0 :=
    crossSection_ne_zero_on_range P hP hn _ _ _ hne_m hgen' hsp'
  obtain ⟨y₀, hy₀gen, hy₀pos⟩ := crossSection_pos_somewhere_generic P horient
  obtain ⟨hy₀1, hy₀2⟩ := spanning_mem_range P ℓ (ℓ + 1) hL hH y₀ hy₀gen
    (spanning_of_crossSection_ne_zero P y₀ (ne_of_gt hy₀pos))
  intro y hgen hsp
  obtain ⟨hy1, hy2⟩ := spanning_mem_range P ℓ (ℓ + 1) hL hH y hgen hsp
  exact crossSection_pos_on_Ioo P _ _ hcont hne y₀ ⟨hy₀1, hy₀2⟩ hy₀pos y ⟨hy1, hy2⟩

/-- **Triangle `hpos`, flat (2-equal) case, highest = upper neighbor.** The triangle
has only two distinct heights (`L.2` and `H.2 = (vert (ℓ+1)).2`); the range
`(L.2, H.2)` has **no** interior vertex, so `c` is continuous (all non-vertex) and
nonvanishing (width only) there — no cross-band needed. -/
lemma triangle_hpos_flat_upper (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (ℓ : ZMod P.n)
    (hL : ∀ j, (toReal (P.vert ℓ)).2 ≤ (toReal (P.vert j)).2)
    (h_lh : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ + 1))).2)
    (hflat : ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert ℓ)).2 ∨
      (toReal (P.vert j)).2 = (toReal (P.vert (ℓ + 1))).2) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 →
      0 < ∫ x, (P.winding (x, y) : ℝ) := by
  have hH : ∀ j, (toReal (P.vert j)).2 ≤ (toReal (P.vert (ℓ + 1))).2 := by
    intro j; rcases hflat j with h | h
    · rw [h]; exact h_lh.le
    · rw [h]
  have hgen_all : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2,
      ∀ i, (toReal (P.vert i)).2 ≠ y' := by
    intro y' hy' i; rcases hflat i with h | h
    · rw [h]; exact ne_of_lt hy'.1
    · rw [h]; exact ne_of_gt hy'.2
  have hsp_all : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2,
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y' ∧ y' < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y' ∧ y' < (toReal (P.vert i)).2)).card ≠ 0 :=
    fun y' hy' => Finset.card_ne_zero.mpr ⟨ℓ,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hy'.1.le, hy'.2⟩⟩⟩
  have hcont : ContinuousOn (fun y => ∫ x, (P.winding (x, y) : ℝ))
      (Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2) :=
    crossSection_continuousOn P _ (fun y' hy' i => (hgen_all y' hy' i).symm)
  have hne : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ + 1))).2,
      (∫ x, (P.winding (x, y') : ℝ)) ≠ 0 :=
    fun y' hy' => crossSection_ne_zero_triangle P hP hn y' (hgen_all y' hy') (hsp_all y' hy')
  obtain ⟨y₀, hy₀gen, hy₀pos⟩ := crossSection_pos_somewhere_generic P horient
  obtain ⟨hy₀1, hy₀2⟩ := spanning_mem_range P ℓ (ℓ + 1) hL hH y₀ hy₀gen
    (spanning_of_crossSection_ne_zero P y₀ (ne_of_gt hy₀pos))
  intro y hgen hsp
  obtain ⟨hy1, hy2⟩ := spanning_mem_range P ℓ (ℓ + 1) hL hH y hgen hsp
  exact crossSection_pos_on_Ioo P _ _ hcont hne y₀ ⟨hy₀1, hy₀2⟩ hy₀pos y ⟨hy1, hy2⟩

/-- **Triangle `hpos`, flat (2-equal) case, highest = lower neighbor** (mirror of
`triangle_hpos_flat_upper`, `H = vert (ℓ-1)`). -/
lemma triangle_hpos_flat_lower (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (ℓ : ZMod P.n)
    (hL : ∀ j, (toReal (P.vert ℓ)).2 ≤ (toReal (P.vert j)).2)
    (h_lh : (toReal (P.vert ℓ)).2 < (toReal (P.vert (ℓ - 1))).2)
    (hflat : ∀ j, (toReal (P.vert j)).2 = (toReal (P.vert ℓ)).2 ∨
      (toReal (P.vert j)).2 = (toReal (P.vert (ℓ - 1))).2) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 →
      0 < ∫ x, (P.winding (x, y) : ℝ) := by
  have hH : ∀ j, (toReal (P.vert j)).2 ≤ (toReal (P.vert (ℓ - 1))).2 := by
    intro j; rcases hflat j with h | h
    · rw [h]; exact h_lh.le
    · rw [h]
  have hgen_all : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2,
      ∀ i, (toReal (P.vert i)).2 ≠ y' := by
    intro y' hy' i; rcases hflat i with h | h
    · rw [h]; exact ne_of_lt hy'.1
    · rw [h]; exact ne_of_gt hy'.2
  have hsp_all : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2,
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y' ∧ y' < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y' ∧ y' < (toReal (P.vert i)).2)).card ≠ 0 := by
    intro y' hy'
    refine Finset.card_ne_zero.mpr ⟨ℓ - 1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨?_, hy'.2⟩⟩⟩
    rw [sub_add_cancel]; exact hy'.1.le
  have hcont : ContinuousOn (fun y => ∫ x, (P.winding (x, y) : ℝ))
      (Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2) :=
    crossSection_continuousOn P _ (fun y' hy' i => (hgen_all y' hy' i).symm)
  have hne : ∀ y' ∈ Set.Ioo (toReal (P.vert ℓ)).2 (toReal (P.vert (ℓ - 1))).2,
      (∫ x, (P.winding (x, y') : ℝ)) ≠ 0 :=
    fun y' hy' => crossSection_ne_zero_triangle P hP hn y' (hgen_all y' hy') (hsp_all y' hy')
  obtain ⟨y₀, hy₀gen, hy₀pos⟩ := crossSection_pos_somewhere_generic P horient
  obtain ⟨hy₀1, hy₀2⟩ := spanning_mem_range P ℓ (ℓ - 1) hL hH y₀ hy₀gen
    (spanning_of_crossSection_ne_zero P y₀ (ne_of_gt hy₀pos))
  intro y hgen hsp
  obtain ⟨hy1, hy2⟩ := spanning_mem_range P ℓ (ℓ - 1) hL hH y hgen hsp
  exact crossSection_pos_on_Ioo P _ _ hcont hne y₀ ⟨hy₀1, hy₀2⟩ hy₀pos y ⟨hy1, hy2⟩

/-- **Triangle `hpos` (all cases).** For a simple, positively-oriented triangle the
cross-section value is positive at every generic spanning height. Case split on the
relative heights of the lowest vertex's two neighbors (upper/lower middle, flat, the
all-equal case ruled out by non-degeneracy). -/
lemma triangle_hpos (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (horient : P.PositivelyOriented) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      (Finset.univ.filter fun i =>
        ((toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2)).card ≠ 0 →
      0 < ∫ x, (P.winding (x, y) : ℝ) := by
  obtain ⟨ℓ, hL⟩ := exists_lowest_vertex P
  rcases lt_trichotomy (toReal (P.vert (ℓ + 1))).2 (toReal (P.vert (ℓ - 1))).2 with h | h | h
  · rcases (hL (ℓ + 1)).lt_or_eq with h2 | h2
    · exact triangle_hpos_upper_strict P hP hn horient ℓ hL h2 h
    · refine triangle_hpos_flat_lower P hP hn horient ℓ hL (by rw [h2]; exact h) ?_
      exact triangle_flat_heights P hn ℓ (ℓ - 1) (Or.inr rfl) (Or.inl h2.symm)
  · rcases (hL (ℓ + 1)).lt_or_eq with h2 | h2
    · refine triangle_hpos_flat_upper P hP hn horient ℓ hL h2 ?_
      exact triangle_flat_heights P hn ℓ (ℓ + 1) (Or.inr h.symm) (Or.inr rfl)
    · exfalso
      have heq2 : (toReal (P.vert ℓ)).2 = (toReal (P.vert (ℓ - 1))).2 := by rw [h2]; exact h
      have hcross : cross (toReal (P.vert ℓ) - toReal (P.vert (ℓ - 1)))
          (toReal (P.vert (ℓ + 1)) - toReal (P.vert (ℓ - 1))) = 0 := by
        unfold cross
        simp only [Prod.fst_sub, Prod.snd_sub]
        rw [h, heq2]; ring
      exact lt_irrefl 0 (hcross ▸ corner_cross_base_pos P hn horient ℓ)
  · rcases (hL (ℓ - 1)).lt_or_eq with h2 | h2
    · exact triangle_hpos_lower_strict P hP hn horient ℓ hL h2 h
    · refine triangle_hpos_flat_upper P hP hn horient ℓ hL (by rw [h2]; exact h) ?_
      exact triangle_flat_heights P hn ℓ (ℓ + 1) (Or.inl h2.symm) (Or.inr rfl)

/-- **Triangle polygonal Jordan property (a.e.).** For a simple, positively-oriented
triangle, `winding ∈ {0,1}` almost everywhere. This is the triangle base case of the
polygonal Jordan curve theorem — the central obstruction that has kept Pick's theorem
out of Lean. With `pick_of_two_ae` it reduces `pick` (for `n=3`) to the lattice-point
count `hcount` alone (no Jordan input left). -/
theorem triangle_h01_ae (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (horient : P.PositivelyOriented) :
    ∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1 :=
  h01_ae_of_nonneg_ae_triangle P hn
    (winding_nonneg_ae_triangle_of_crossSection_pos P hn (triangle_hpos P hP hn horient))

end Pick
