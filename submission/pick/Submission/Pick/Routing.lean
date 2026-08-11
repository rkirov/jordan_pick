import Submission.Pick.Slab

/-!
# Pick's theorem: inside-connectivity routing (Module 5b: cross-level + apex-cross)

Continues `Pick.Slab`: cross-vertex-level routing (`lift_across_level`),
apex-cross, and inside connectivity. Lives inside `namespace Pick`.
-/

namespace Pick

open LatticePolygon

variable (P : LatticePolygon)

section InsideConnected

open LatticePolygon MeasureTheory

/-! ### Cross-vertex-level routing (`lift_across_level`)

The slab-routing lemmas connect points at *generic* heights `y₁ < y₂` whose open
slab is vertex-free. To route across a single vertex level `w`, we must show the
horizontal segment of the gap stays off the boundary *at the level `w` itself*.
`gap_clear_at_level_of_no_vertex` is the level-`w` clearance primitive. -/

/-- **Gap clearance at the exact vertex level `w`.** A point `(xm, w)` whose abscissa
lies strictly inside `(L, R)` is off the boundary, provided every potential incidence
is excluded: (`hspan_gap`) every edge that crosses `w` strictly has its threshold
outside `(L, R)`; (`hvert_abs`) every vertex exactly at height `w` has its abscissa
outside the open gap; and (`hhoriz`) no edge with *both* endpoints at height `w`
(a horizontal edge) meets the open gap. Proof: a boundary point lies on some
`edgeSeg j`; split on whether each endpoint is at `w`. Both-off ⟹ `j` spans and
`xm = edgeThr w j` (excluded by `hspan_gap`); both-at ⟹ horizontal edge (excluded by
`hhoriz`); exactly-one-at ⟹ height `w` is attained only at that endpoint, so
`(xm,w)` is that vertex and `xm` is its abscissa (excluded by `hvert_abs`). -/
lemma gap_clear_at_level_of_no_vertex (w L R xm : ℝ)
    (hxm : L < xm ∧ xm < R)
    (hspan_gap : ∀ j, (toReal (P.vert j)).2 ≠ w → (toReal (P.vert (j+1))).2 ≠ w →
        (((toReal (P.vert j)).2 < w ∧ w < (toReal (P.vert (j+1))).2) ∨
         ((toReal (P.vert (j+1))).2 < w ∧ w < (toReal (P.vert j)).2)) →
        P.edgeThr w j ≤ L ∨ R ≤ P.edgeThr w j)
    (hvert_abs : ∀ k, (toReal (P.vert k)).2 = w →
        (toReal (P.vert k)).1 ≤ L ∨ R ≤ (toReal (P.vert k)).1)
    (hhoriz : ∀ j, (toReal (P.vert j)).2 = w → (toReal (P.vert (j+1))).2 = w →
        ∀ x, ((x, w) : ℝ × ℝ) ∈ P.edgeSeg j → x ≤ L ∨ R ≤ x) :
    ((xm, w) : ℝ × ℝ) ∉ P.boundary := by
  rintro ⟨_, ⟨j, rfl⟩, hxjraw⟩
  -- `(xm, w) ∈ edgeSeg j`
  have hxjseg : (xm, w) ∈ P.edgeSeg j := hxjraw
  have hxj : (xm, w) ∈ segment ℝ (toReal (P.vert j)) (toReal (P.vert (j+1))) := by
    rw [LatticePolygon.edgeSeg] at hxjseg; exact hxjseg
  set a := toReal (P.vert j) with ha
  set b := toReal (P.vert (j+1)) with hb
  by_cases haw : a.2 = w
  · by_cases hbw : b.2 = w
    · -- horizontal edge at w
      rcases hhoriz j haw hbw xm hxjseg with h | h
      · linarith [hxm.1]
      · linarith [hxm.2]
    · -- a at w, b off w: the only point of the segment at height w is a
      have hpt : (xm, w) = a := by
        rw [segment_eq_image] at hxj
        obtain ⟨t, ht, hxy⟩ := hxj
        rw [Prod.ext_iff] at hxy
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] at hxy
        obtain ⟨hx, hyt⟩ := hxy
        -- (1-t)*a.2 + t*b.2 = w, a.2 = w, b.2 ≠ w ⟹ t = 0
        have ht0 : t = 0 := by
          rcases eq_or_lt_of_le ht.1 with h0 | h0
          · linarith
          · exfalso; apply hbw
            have : (1 - t) * a.2 + t * b.2 = w := hyt
            rw [haw] at this
            have : t * b.2 = t * w := by nlinarith
            have := mul_left_cancel₀ (ne_of_gt h0) this; linarith
        rw [Prod.ext_iff]
        constructor
        · simp only; rw [← hx, ht0]; ring
        · simp only; rw [← haw]
      have : xm = a.1 := by rw [Prod.ext_iff] at hpt; exact hpt.1
      rcases hvert_abs j haw with h | h
      · rw [this] at hxm; linarith [hxm.1]
      · rw [this] at hxm; linarith [hxm.2]
  · by_cases hbw : b.2 = w
    · -- b at w, a off w: the only point at height w is b = vert (j+1)
      have hpt : (xm, w) = b := by
        rw [segment_eq_image] at hxj
        obtain ⟨t, ht, hxy⟩ := hxj
        rw [Prod.ext_iff] at hxy
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] at hxy
        obtain ⟨hx, hyt⟩ := hxy
        have ht1 : t = 1 := by
          rcases eq_or_lt_of_le ht.2 with h1 | h1
          · exact h1
          · exfalso; apply haw
            have : (1 - t) * a.2 + t * b.2 = w := hyt
            rw [hbw] at this
            have hcanc : (1 - t) * a.2 = (1 - t) * w := by nlinarith
            have h1t : (1 : ℝ) - t ≠ 0 := by intro h; linarith
            have := mul_left_cancel₀ h1t hcanc; linarith
        rw [Prod.ext_iff]
        constructor
        · simp only; rw [← hx, ht1]; ring
        · simp only; rw [← hbw]
      have : xm = b.1 := by rw [Prod.ext_iff] at hpt; exact hpt.1
      rcases hvert_abs (j+1) hbw with h | h
      · rw [this] at hxm; linarith [hxm.1]
      · rw [this] at hxm; linarith [hxm.2]
    · -- both off w: j spans w and xm = edgeThr w j
      obtain ⟨hxeq, hspan⟩ :=
        eq_threshold_of_mem_segment_horizontal a b w xm (Ne.symm haw) (Ne.symm hbw) hxj
      have hthreq : P.edgeThr w j = crossThreshold a b w := by rw [LatticePolygon.edgeThr]
      rcases hspan_gap j haw hbw hspan with h | h
      · rw [hthreq] at h; rw [hxeq] at hxm; linarith [hxm.1]
      · rw [hthreq] at h; rw [hxeq] at hxm; linarith [hxm.2]

/-- **A fixed abscissa stays in the chord gap near a level `w`.** If `xm` lies
strictly between the two thresholds `edgeThr w i` and `edgeThr w i'` of two
non-horizontal edges, then by continuity of `edgeThr · ·` in the height there is a
two-sided neighbourhood `(w - δ, w + δ)` on which `xm` is still strictly between the
two thresholds. This lets a *vertical* probe at abscissa `xm` cross the level `w`
while remaining inside the moving gap (hence off the boundary in the vertex-free
slabs on either side). -/
lemma gap_persists_near_level (i i' : ZMod P.n) (w xm : ℝ)
    (hdi : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2)
    (hdi' : (toReal (P.vert (i'+1))).2 ≠ (toReal (P.vert i')).2)
    (hL : P.edgeThr w i < xm) (hR : xm < P.edgeThr w i') :
    ∃ δ > 0, ∀ t, w - δ < t → t < w + δ →
      P.edgeThr t i < xm ∧ xm < P.edgeThr t i' := by
  have hci : Continuous (fun t => P.edgeThr t i) := by
    unfold LatticePolygon.edgeThr crossThreshold
    have : (toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2 ≠ 0 := sub_ne_zero.mpr hdi
    fun_prop (disch := assumption)
  have hci' : Continuous (fun t => P.edgeThr t i') := by
    unfold LatticePolygon.edgeThr crossThreshold
    have : (toReal (P.vert (i'+1))).2 - (toReal (P.vert i')).2 ≠ 0 := sub_ne_zero.mpr hdi'
    fun_prop (disch := assumption)
  have h1 : ∀ᶠ t in nhds w, P.edgeThr t i < xm :=
    (hci.continuousAt).eventually_lt continuousAt_const hL
  have h2 : ∀ᶠ t in nhds w, xm < P.edgeThr t i' :=
    continuousAt_const.eventually_lt (hci'.continuousAt) hR
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  refine ⟨δ, hδ, fun t htlo hthi => ?_⟩
  exact hball t (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)

/-- **A point of the consecutive-gap column is off the boundary, at every slab
height.** In a vertex-free open slab `(y₁, y₂)` with two consecutive spanning
chords `iL, iR` at a generic reference height `y` (no spanning threshold strictly
between, `hcons`), any point `(xm, t)` whose abscissa `xm` lies strictly between the
two chords *at its own height* `t ∈ (y₁, y₂)` is off the boundary. Proof: `t` is
generic, the spanning set is constant across the slab, and chord order is preserved
(`chord_order_preserved_in_slab`), so every spanning threshold at `t` is `≤ edgeThr t
iL` or `≥ edgeThr t iR`; `notMem_boundary_of_between_thresholds` finishes. The
clearance fact for a *vertical* probe rising through the gap toward the level `w`. -/
lemma notMem_boundary_in_consecutive_gap (hP : P.IsSimple) (y₁ y₂ : ℝ)
    (hslab : ∀ i, ¬ (y₁ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y₂))
    (iL iR : ZMod P.n) {y : ℝ} (hy : y ∈ Set.Ioo y₁ y₂)
    (hiL : iL ∈ P.spanningSet y) (hiR : iR ∈ P.spanningSet y)
    (hcons : ∀ k ∈ P.spanningSet y,
      P.edgeThr y k ≤ P.edgeThr y iL ∨ P.edgeThr y iR ≤ P.edgeThr y k)
    {t xm : ℝ} (ht : t ∈ Set.Ioo y₁ y₂)
    (hxmL : P.edgeThr t iL < xm) (hxmR : xm < P.edgeThr t iR) :
    ((xm, t) : ℝ × ℝ) ∉ P.boundary := by
  have hgen : ∀ z, z ∈ Set.Ioo y₁ y₂ → ∀ k, (toReal (P.vert k)).2 ≠ z :=
    fun z hz k hk => hslab k ⟨hk ▸ hz.1, hk ▸ hz.2⟩
  have hconst : ∀ z, z ∈ Set.Ioo y₁ y₂ → P.spanningSet z = P.spanningSet y :=
    fun z hz => spanningSet_const_of_slab P y₁ y₂ hslab hz hy
  refine notMem_boundary_of_between_thresholds P t (hgen t ht) xm
    (P.edgeThr t iL) (P.edgeThr t iR) ⟨hxmL, hxmR⟩ ?_
  intro k hk
  have hkY : k ∈ P.spanningSet y := by rw [← hconst t ht]; exact hk
  rcases hcons k hkY with hle | hge
  · left
    by_cases hkiL : k = iL
    · rw [hkiL]
    · have hd : P.edgeThr y k ≠ P.edgeThr y iL :=
        crossThreshold_ne_distinct_spanning P hP y (hgen y hy) k iL hkiL
          (by simpa [LatticePolygon.spanningSet, Finset.mem_filter] using hkY)
          (by simpa [LatticePolygon.spanningSet, Finset.mem_filter] using hiL)
      exact le_of_lt (chord_order_preserved_in_slab P hP y₁ y₂ hslab k iL hy hkY hiL
        (lt_of_le_of_ne hle hd) ht)
  · right
    by_cases hkiR : k = iR
    · rw [hkiR]
    · have hd : P.edgeThr y iR ≠ P.edgeThr y k :=
        crossThreshold_ne_distinct_spanning P hP y (hgen y hy) iR k (Ne.symm hkiR)
          (by simpa [LatticePolygon.spanningSet, Finset.mem_filter] using hiR)
          (by simpa [LatticePolygon.spanningSet, Finset.mem_filter] using hkY)
      exact le_of_lt (chord_order_preserved_in_slab P hP y₁ y₂ hslab iR k hy hiR hkY
        (lt_of_le_of_ne hge hd) ht)


/-- **Lift a gap-interior point across one vertex level `w` (level-`w` clearance
supplied).** Generic heights `y < w < y'` whose two open slabs `(y, w)` and `(w, y')`
are vertex-free; two consecutive spanning chords `iL, iR` (no spanning threshold
strictly between) survive across the level, spanning `y`, `w`, and `y'` with
`edgeThr · iL < edgeThr · iR` at each; `x` lies in the gap at `y`, `x'` in the gap at
`y'`. Given the *level-`w` clearance* `hwclear` — every abscissa strictly inside the
`w`-gap is off the boundary (the obligation discharged by
`gap_clear_at_level_of_no_vertex` in the no-`w`-vertex-in-gap case) — the two interior
points are `JoinedIn boundaryᶜ`. The route: slab-gap from `(x,y)` up to `(xm,y₁)`
(`joinedIn_consecutive_gap_in_slab`), a vertical probe at the gap-midpoint `xm`
crossing the level `w` (`notMem_boundary_in_consecutive_gap` below `w`, `gap_persists_near_level`
to keep `xm` inside, `hwclear` at `w`), then slab-gap from `(xm,y₂)` to `(x',y')`. -/
lemma lift_across_level (hP : P.IsSimple) (y w y' : ℝ)
    (hyw : y < w) (hwy' : w < y')
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y) (hy'gen : ∀ i, (toReal (P.vert i)).2 ≠ y')
    (hslabL : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w))
    (hslabR : ∀ i, ¬ (w < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y'))
    (iL iR : ZMod P.n)
    (hiL_y : iL ∈ P.spanningSet y) (hiR_y : iR ∈ P.spanningSet y)
    (hLR_y : P.edgeThr y iL < P.edgeThr y iR)
    (hcons_y : ∀ k ∈ P.spanningSet y,
      P.edgeThr y k ≤ P.edgeThr y iL ∨ P.edgeThr y iR ≤ P.edgeThr y k)
    (hiL_y' : iL ∈ P.spanningSet y') (hiR_y' : iR ∈ P.spanningSet y')
    (hLR_y' : P.edgeThr y' iL < P.edgeThr y' iR)
    (hcons_y' : ∀ k ∈ P.spanningSet y',
      P.edgeThr y' k ≤ P.edgeThr y' iL ∨ P.edgeThr y' iR ≤ P.edgeThr y' k)
    (hiL_w : iL ∈ P.spanningSet w) (hiR_w : iR ∈ P.spanningSet w)
    (hLR_w : P.edgeThr w iL < P.edgeThr w iR)
    (hwclear : ∀ xm, P.edgeThr w iL < xm → xm < P.edgeThr w iR →
      ((xm, w) : ℝ × ℝ) ∉ P.boundary)
    (x x' : ℝ)
    (hx : P.edgeThr y iL < x ∧ x < P.edgeThr y iR)
    (hx' : P.edgeThr y' iL < x' ∧ x' < P.edgeThr y' iR) :
    JoinedIn P.boundaryᶜ (x, y) (x', y') := by
  classical
  -- the gap midpoint at level `w`
  set xm := (P.edgeThr w iL + P.edgeThr w iR) / 2 with hxmdef
  have hxmL_w : P.edgeThr w iL < xm := by rw [hxmdef]; linarith
  have hxmR_w : xm < P.edgeThr w iR := by rw [hxmdef]; linarith
  -- non-horizontality of the two chords (from spanning at `w`)
  have hspan_w : ∀ k ∈ P.spanningSet w,
      ((toReal (P.vert k)).2 < w ∧ w < (toReal (P.vert (k + 1))).2) ∨
      ((toReal (P.vert (k + 1))).2 < w ∧ w < (toReal (P.vert k)).2) := by
    intro k hk; simpa [LatticePolygon.spanningSet, Finset.mem_filter] using hk
  have hdiL : (toReal (P.vert (iL+1))).2 ≠ (toReal (P.vert iL)).2 := by
    rcases hspan_w iL hiL_w with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> · intro h; linarith
  have hdiR : (toReal (P.vert (iR+1))).2 ≠ (toReal (P.vert iR)).2 := by
    rcases hspan_w iR hiR_w with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> · intro h; linarith
  -- gap persists in a two-sided neighbourhood of `w`
  obtain ⟨δ, hδ, hpers⟩ := gap_persists_near_level P iL iR w xm hdiL hdiR hxmL_w hxmR_w
  -- extend a vertex-free slab below `y` and above `y'`, so `y`, `y'` are interior
  obtain ⟨y₀, hy₀y, hslab0⟩ := exists_vertexFree_slab_below P y w hygen hslabL
  -- mirror: extend above `y'`. Build the upper slab `(w, y₃)` with `y' < y₃` interior.
  obtain ⟨y₃, hy'y₃, hslab3⟩ : ∃ y₃, y' < y₃ ∧
      ∀ i, ¬ (w < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y₃) := by
    classical
    set S := Finset.univ.filter (fun i => y' < (toReal (P.vert i)).2) with hS
    by_cases hSne : S.Nonempty
    · obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun i => (toReal (P.vert i)).2) hSne
      rw [hS, Finset.mem_filter] at hmS
      refine ⟨((toReal (P.vert m)).2 + y') / 2, by linarith [hmS.2], ?_⟩
      intro i ⟨h1, h2⟩
      rcases lt_trichotomy (toReal (P.vert i)).2 y' with hlt | heq | hgt
      · exact hslabR i ⟨h1, hlt⟩
      · exact hy'gen i heq
      · have := hmin i (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩); linarith
    · refine ⟨y' + 1, by linarith, ?_⟩
      intro i ⟨h1, h2⟩
      rcases lt_trichotomy (toReal (P.vert i)).2 y' with hlt | heq | hgt
      · exact hslabR i ⟨h1, hlt⟩
      · exact hy'gen i heq
      · exact hSne ⟨i, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩⟩
  -- pick a generic height `y₁ ∈ (max y₀ (w-δ) ... , w)` close to `w`, and below `w`
  set lo₁ := max y₀ (w - δ) with hlo₁
  have hlo₁w : lo₁ < w := by
    rw [hlo₁]; refine max_lt ?_ (by linarith)
    exact lt_trans hy₀y hyw
  obtain ⟨y₁, hy₁lo, hy₁hi, hy₁gen⟩ := exists_generic_height_mem_Ioo P lo₁ w hlo₁w
  have hy₁_in0 : y₁ ∈ Set.Ioo y₀ w :=
    ⟨lt_of_le_of_lt (le_max_left _ _) hy₁lo, hy₁hi⟩
  have hy₁_pers : w - δ < y₁ := lt_of_le_of_lt (le_max_right _ _) hy₁lo
  -- pick a generic height `y₂ ∈ (w, min y₃ (w+δ))` close to `w`, above `w`
  set hi₂ := min y₃ (w + δ) with hhi₂
  have hwhi₂ : w < hi₂ := by
    rw [hhi₂]; refine lt_min ?_ (by linarith)
    exact lt_trans hwy' hy'y₃
  obtain ⟨y₂, hy₂lo, hy₂hi, hy₂gen⟩ := exists_generic_height_mem_Ioo P w hi₂ hwhi₂
  have hy₂_in3 : y₂ ∈ Set.Ioo w y₃ :=
    ⟨hy₂lo, lt_of_lt_of_le hy₂hi (min_le_left _ _)⟩
  have hy₂_pers : y₂ < w + δ := lt_of_lt_of_le hy₂hi (min_le_right _ _)
  -- gap values at `y₁` and `y₂`
  obtain ⟨hgapL₁, hgapR₁⟩ := hpers y₁ (by linarith) (by linarith)
  obtain ⟨hgapL₂, hgapR₂⟩ := hpers y₂ (by linarith) (by linarith)
  -- STEP 1: (x, y) → (xm, y₁) in lower slab (y₀, w)
  have hstep1 : JoinedIn P.boundaryᶜ (x, y) (xm, y₁) := by
    refine joinedIn_consecutive_gap_in_slab P hP y₀ w hslab0 iL iR
      (y := y) ⟨hy₀y, hyw⟩ hiL_y hiR_y hLR_y hcons_y
      ⟨⟨hy₀y, hyw⟩, hx.1, hx.2⟩ ⟨hy₁_in0, hgapL₁, hgapR₁⟩
  -- STEP 2: (xm, y₁) → (xm, w) vertical, crossing into level w
  have hstep2 : JoinedIn P.boundaryᶜ (xm, y₁) (xm, w) := by
    refine joinedIn_vertical_of_endpoints P xm y₁ w (le_of_lt hy₁hi) ?_ ?_ ?_
    · exact notMem_boundary_in_consecutive_gap P hP y₀ w hslab0 iL iR ⟨hy₀y, hyw⟩
        hiL_y hiR_y hcons_y hy₁_in0 hgapL₁ hgapR₁
    · exact hwclear xm hxmL_w hxmR_w
    · intro t htlo hthi
      obtain ⟨hgL, hgR⟩ := hpers t (by linarith) (by linarith)
      exact notMem_boundary_in_consecutive_gap P hP y₀ w hslab0 iL iR ⟨hy₀y, hyw⟩
        hiL_y hiR_y hcons_y ⟨lt_trans hy₁_in0.1 htlo, hthi⟩ hgL hgR
  -- STEP 3: (xm, w) → (xm, y₂) vertical, crossing out of level w
  have hstep3 : JoinedIn P.boundaryᶜ (xm, w) (xm, y₂) := by
    refine joinedIn_vertical_of_endpoints P xm w y₂ (le_of_lt hy₂lo) ?_ ?_ ?_
    · exact hwclear xm hxmL_w hxmR_w
    · exact notMem_boundary_in_consecutive_gap P hP w y₃ hslab3 iL iR ⟨hwy', hy'y₃⟩
        hiL_y' hiR_y' hcons_y' hy₂_in3 hgapL₂ hgapR₂
    · intro t htlo hthi
      obtain ⟨hgL, hgR⟩ := hpers t (by linarith) (by linarith)
      exact notMem_boundary_in_consecutive_gap P hP w y₃ hslab3 iL iR ⟨hwy', hy'y₃⟩
        hiL_y' hiR_y' hcons_y' ⟨htlo, lt_trans hthi hy₂_in3.2⟩ hgL hgR
  -- STEP 4: (xm, y₂) → (x', y') in upper slab (w, y₃)
  have hstep4 : JoinedIn P.boundaryᶜ (xm, y₂) (x', y') := by
    refine joinedIn_consecutive_gap_in_slab P hP w y₃ hslab3 iL iR
      (y := y') ⟨hwy', hy'y₃⟩ hiL_y' hiR_y' hLR_y' hcons_y'
      ⟨hy₂_in3, hgapL₂, hgapR₂⟩ ⟨⟨hwy', hy'y₃⟩, hx'.1, hx'.2⟩
  exact ((hstep1.trans hstep2).trans hstep3).trans hstep4

/-- **Discharge the level-`w` clearance `hwclear` of `lift_across_level` from
consecutivity at `w`.** Given two spanning chords `iL, iR` at the level `w` with no
*other* spanning threshold strictly between them (`hcons_w`), no vertex at height `w`
whose abscissa lies in the open gap `(edgeThr w iL, edgeThr w iR)` (`hvert_abs`), and
no horizontal `w`-edge meeting the gap (`hhoriz`), every abscissa strictly inside the
`w`-gap is off the boundary. This is exactly `gap_clear_at_level_of_no_vertex` applied
with `L := edgeThr w iL`, `R := edgeThr w iR`: its `hspan_gap` obligation (a spanning
edge keeps its threshold outside the gap) is precisely `hcons_w` once the crossing
disjunction is repackaged as `spanningSet` membership. -/
lemma hwclear_of_consecutive (w : ℝ) (iL iR : ZMod P.n)
    (hcons_w : ∀ k ∈ P.spanningSet w,
      P.edgeThr w k ≤ P.edgeThr w iL ∨ P.edgeThr w iR ≤ P.edgeThr w k)
    (hvert_abs : ∀ k, (toReal (P.vert k)).2 = w →
        (toReal (P.vert k)).1 ≤ P.edgeThr w iL ∨ P.edgeThr w iR ≤ (toReal (P.vert k)).1)
    (hhoriz : ∀ j, (toReal (P.vert j)).2 = w → (toReal (P.vert (j+1))).2 = w →
        ∀ x, ((x, w) : ℝ × ℝ) ∈ P.edgeSeg j →
          x ≤ P.edgeThr w iL ∨ P.edgeThr w iR ≤ x) :
    ∀ xm, P.edgeThr w iL < xm → xm < P.edgeThr w iR →
      ((xm, w) : ℝ × ℝ) ∉ P.boundary := by
  intro xm hxmL hxmR
  refine gap_clear_at_level_of_no_vertex P w (P.edgeThr w iL) (P.edgeThr w iR) xm
    ⟨hxmL, hxmR⟩ ?_ hvert_abs hhoriz
  intro j hj hj1 hcross
  refine hcons_w j ?_
  simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hcross

/-- **Open a vertex-free slab upward above a generic height.** Mirror of
`exists_vertexFree_slab_below`: if `y'` is generic and the open slab `(w, y')`
contains no vertex height, there is `y₁ > y'` with `(w, y₁)` still vertex-free. This
makes `y'` lie strictly inside a vertex-free slab. -/
lemma exists_vertexFree_slab_above (w y' : ℝ)
    (hgen : ∀ i, (toReal (P.vert i)).2 ≠ y')
    (hno : ∀ i, ¬ (w < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y')) :
    ∃ y₁, y' < y₁ ∧ ∀ i, ¬ (w < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y₁) := by
  classical
  set S := Finset.univ.filter (fun i => y' < (toReal (P.vert i)).2) with hS
  by_cases hSne : S.Nonempty
  · obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun i => (toReal (P.vert i)).2) hSne
    rw [hS, Finset.mem_filter] at hmS
    refine ⟨((toReal (P.vert m)).2 + y')/2, by linarith [hmS.2], ?_⟩
    intro i ⟨h1, h2⟩
    rcases lt_trichotomy (toReal (P.vert i)).2 y' with hlt | heq | hgt
    · exact hno i ⟨h1, hlt⟩
    · exact hgen i heq
    · have := hmin i (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩); linarith
  · refine ⟨y' + 1, by linarith, ?_⟩
    intro i ⟨h1, h2⟩
    rcases lt_trichotomy (toReal (P.vert i)).2 y' with hlt | heq | hgt
    · exact hno i ⟨h1, hlt⟩
    · exact hgen i heq
    · exact hSne ⟨i, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩⟩

/-- **Lift a gap point across a vertex-free slab.** Two generic heights `y < y'`
whose open slab `(y, y')` contains no vertex height; two consecutive spanning chords
`iL, iR` survive both ends (spanning + ordered + no spanning threshold strictly
between). A gap-interior point at `y` connects to a gap-interior point at `y'`. This
is the *single-slab* base step: extend the slab on both sides
(`exists_vertexFree_slab_below`/`_above`) so `y, y'` are strictly interior, then
`joinedIn_consecutive_gap_in_slab`. -/
lemma lift_within_vertexFree_slab (hP : P.IsSimple) (y y' : ℝ)
    (hyy' : y < y')
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y) (hy'gen : ∀ i, (toReal (P.vert i)).2 ≠ y')
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y'))
    (iL iR : ZMod P.n)
    (hiL_y : iL ∈ P.spanningSet y) (hiR_y : iR ∈ P.spanningSet y)
    (hLR_y : P.edgeThr y iL < P.edgeThr y iR)
    (hcons_y : ∀ k ∈ P.spanningSet y,
      P.edgeThr y k ≤ P.edgeThr y iL ∨ P.edgeThr y iR ≤ P.edgeThr y k)
    (x x' : ℝ)
    (hx : P.edgeThr y iL < x ∧ x < P.edgeThr y iR)
    (hx' : P.edgeThr y' iL < x' ∧ x' < P.edgeThr y' iR) :
    JoinedIn P.boundaryᶜ (x, y) (x', y') := by
  obtain ⟨y₀, hy₀y, hslab0⟩ := exists_vertexFree_slab_below P y y' hygen hslab
  obtain ⟨y₁, hy'y₁, hslab1⟩ := exists_vertexFree_slab_above P y y' hy'gen hslab
  -- merge the two enlargements into one vertex-free slab (y₀, y₁) containing y, y'
  have hslabM : ∀ i, ¬ (y₀ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < y₁) := by
    intro i ⟨h1, h2⟩
    rcases lt_trichotomy (toReal (P.vert i)).2 y' with hlt' | heq' | hgt'
    · exact hslab0 i ⟨h1, hlt'⟩
    · exact hy'gen i heq'
    · exact hslab1 i ⟨lt_trans hyy' hgt', h2⟩
  have hyM : y ∈ Set.Ioo y₀ y₁ := ⟨hy₀y, lt_trans hyy' hy'y₁⟩
  have hy'M : y' ∈ Set.Ioo y₀ y₁ := ⟨lt_trans hy₀y hyy', hy'y₁⟩
  exact joinedIn_consecutive_gap_in_slab P hP y₀ y₁ hslabM iL iR (y := y) hyM
    hiL_y hiR_y hLR_y hcons_y (p := (x, y)) ⟨hyM, hx.1, hx.2⟩
    (q := (x', y')) ⟨hy'M, hx'.1, hx'.2⟩

/-- **Nearest spanning neighbour below a chord, with consecutivity.** At a generic
height `y`, given a spanning edge `e`, if *some* spanning edge has threshold strictly
below `edgeThr y e`, then there is a spanning edge `eL` whose threshold is the largest
such — so `edgeThr y eL < edgeThr y e` and no spanning threshold lies strictly in the
open gap `(edgeThr y eL, edgeThr y e)`. The left consecutive bounding chord of the gap
just left of `e`. -/
lemma exists_consecutive_below (y : ℝ)
    (e : ZMod P.n)
    (hex : ∃ k ∈ P.spanningSet y, P.edgeThr y k < P.edgeThr y e) :
    ∃ eL ∈ P.spanningSet y, P.edgeThr y eL < P.edgeThr y e ∧
      ∀ k ∈ P.spanningSet y, P.edgeThr y k ≤ P.edgeThr y eL ∨
        P.edgeThr y e ≤ P.edgeThr y k := by
  classical
  set S := (P.spanningSet y).filter (fun k => P.edgeThr y k < P.edgeThr y e) with hS
  have hSne : S.Nonempty := by obtain ⟨k, hk, hlt⟩ := hex; exact ⟨k, by rw [hS, Finset.mem_filter]; exact ⟨hk, hlt⟩⟩
  obtain ⟨eL, heLS, heLmax⟩ := S.exists_max_image (P.edgeThr y) hSne
  rw [hS, Finset.mem_filter] at heLS
  obtain ⟨heLspan, heLlt⟩ := heLS
  refine ⟨eL, heLspan, heLlt, ?_⟩
  intro k hk
  by_cases hke : P.edgeThr y k < P.edgeThr y e
  · exact Or.inl (heLmax k (by rw [hS, Finset.mem_filter]; exact ⟨hk, hke⟩))
  · exact Or.inr (not_lt.mp hke)

/-- **Isolating ball uniform over a horizontal top run.** Given a run of vertices
`p, p+1, …, p+L` (indices `p + (t : ℕ)` for `t : Fin (L+1)`), there is a single radius
`r > 0` such that every edge `j` that is *not* a run-incident edge — i.e. `j ≠ p-1` and
`j ≠ p + t` for all `t : Fin (L+1)` — is `r`-isolated from *every* run vertex. Built as
the finite min of the per-vertex isolating radii of `exists_isolating_ball`, intersected
so a non-incident edge stays clear of all run vertices at once. -/
lemma plateau_isolating_ball (hsimple : P.IsSimple) (p : ZMod P.n) (L : ℕ) :
    ∃ r > 0, ∀ (t : Fin (L + 1)) (j : ZMod P.n),
      (∀ s : Fin (L + 1), j ≠ p + (s : ℕ)) → j ≠ p - 1 →
      Disjoint (Metric.ball (toReal (P.vert (p + (t : ℕ)))) r) (P.edgeSeg j) := by
  classical
  -- per-vertex isolating radii for each run vertex p + t
  choose rr hrr hball using fun t : Fin (L + 1) => exists_isolating_ball P hsimple (p + (t : ℕ))
  refine ⟨Finset.univ.inf' ⟨0, Finset.mem_univ 0⟩ rr, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun t _ => hrr t)
  · intro t j hjrun hjm1
    -- at vertex p + t, the only incident edges are (p+t)-1 and (p+t); both excluded
    have hne1 : j ≠ p + (t : ℕ) := hjrun t
    have hne2 : j ≠ (p + (t : ℕ)) - 1 := by
      rcases (t : ℕ).eq_zero_or_pos with h0 | hpos
      · -- t = 0 : (p+0)-1 = p-1, excluded by hjm1
        simp only [h0, Nat.cast_zero, add_zero] at *
        exact hjm1
      · -- t ≥ 1 : (p+t)-1 = p + (t-1), which is a run index
        have hcast : (p + (t : ℕ)) - 1 = p + ((t : ℕ) - 1 : ℕ) := by
          have : ((t : ℕ) : ZMod P.n) = (((t : ℕ) - 1 : ℕ) : ZMod P.n) + 1 := by
            rw [Nat.cast_sub hpos]; push_cast; ring
          rw [this]; ring
        rw [hcast]
        have hlt : (t : ℕ) - 1 < L + 1 := by omega
        have := hjrun ⟨(t : ℕ) - 1, hlt⟩
        simpa only [Fin.val_mk] using this
    have hsub : Finset.univ.inf' ⟨0, Finset.mem_univ 0⟩ rr ≤ rr t :=
      Finset.inf'_le _ (Finset.mem_univ t)
    exact Set.disjoint_of_subset_left (Metric.ball_subset_ball hsub) (hball t j hne1 hne2)

/-- **Two non-adjacent edges are uniformly separated.** If `i, j` are distinct,
non-adjacent edges (`i ≠ j`, `i+1 ≠ j`, `j+1 ≠ i`), there is `r > 0` with `dist x x' ≥ r`
for every `x ∈ edgeSeg i`, `x' ∈ edgeSeg j`: the two disjoint compact segments have
positive `infDist`, and `r` is half of it. -/
lemma edges_uniformly_separated (hsimple : P.IsSimple) (i j : ZMod P.n)
    (hij : i ≠ j) (hij1 : i + 1 ≠ j) (hji1 : j + 1 ≠ i) :
    ∃ r > 0, ∀ x ∈ P.edgeSeg i, ∀ x' ∈ P.edgeSeg j, r ≤ dist x x' := by
  have hdisj : Disjoint (P.edgeSeg i) (P.edgeSeg j) := hsimple.2.1 i j hij hij1 hji1
  have hci : IsCompact (P.edgeSeg i) := isCompact_edgeSeg P i
  have hcj : IsCompact (P.edgeSeg j) := isCompact_edgeSeg P j
  have hnei : (P.edgeSeg i).Nonempty :=
    ⟨toReal (P.vert i), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩
  have hnej : (P.edgeSeg j).Nonempty :=
    ⟨toReal (P.vert j), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩
  -- minimise dist over the compact product edgeSeg i ×ˢ edgeSeg j
  have hcprod : IsCompact (P.edgeSeg i ×ˢ P.edgeSeg j) := hci.prod hcj
  have hprodne : (P.edgeSeg i ×ˢ P.edgeSeg j).Nonempty := hnei.prod hnej
  have hcont : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => dist z.1 z.2)
      (P.edgeSeg i ×ˢ P.edgeSeg j) := (continuous_dist).continuousOn
  obtain ⟨z₀, hz₀mem, hz₀min⟩ := hcprod.exists_isMinOn hprodne hcont
  have hz₀pos : 0 < dist z₀.1 z₀.2 := by
    rw [dist_pos]
    intro heq
    exact Set.disjoint_left.mp hdisj hz₀mem.1 (heq ▸ hz₀mem.2)
  refine ⟨dist z₀.1 z₀.2, hz₀pos, fun x hx x' hx' => ?_⟩
  exact hz₀min (Set.mk_mem_prod hx hx')

/-- **Segment isolating ball, uniform over a horizontal top run.** For the `L` horizontal
run edges `p, …, p+L-1` (indices `p + (t : ℕ)`, `t : Fin L`), there is `r > 0` such that
every non-run-incident edge `j` (`j ≠ p-1`, and `j ≠ p+s` for all `s : Fin (L+1)`) keeps
distance `≥ r` from *every* point of *every* run edge segment. From simplicity: a
non-incident edge is non-adjacent to each run edge (`edges_uniformly_separated`); take the
finite min of the per-edge separations. -/
lemma plateau_seg_isolating_ball (hsimple : P.IsSimple) (p : ZMod P.n) (L : ℕ) :
    ∃ r > 0, ∀ (t : Fin L) (j : ZMod P.n),
      (∀ s : Fin (L + 1), j ≠ p + (s : ℕ)) → j ≠ p - 1 →
      ∀ x ∈ P.edgeSeg (p + (t : ℕ)), ∀ x' ∈ P.edgeSeg j, r ≤ dist x x' := by
  classical
  -- non-adjacency of a run edge `p+t` to any non-incident edge `j`
  have hnonadj : ∀ (t : Fin L) (j : ZMod P.n),
      (∀ s : Fin (L + 1), j ≠ p + (s : ℕ)) → j ≠ p - 1 →
      (p + (t : ℕ)) ≠ j ∧ (p + (t : ℕ)) + 1 ≠ j ∧ j + 1 ≠ (p + (t : ℕ)) := by
    intro t j hjrun hjm1
    have htL1 : (t : ℕ) < L + 1 := by omega
    have ht1L1 : (t : ℕ) + 1 < L + 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · have := hjrun ⟨(t : ℕ), htL1⟩; simp only [] at this; exact (this.symm)
    · have := hjrun ⟨(t : ℕ) + 1, ht1L1⟩; simp only [] at this
      have hcast : p + (t : ℕ) + 1 = p + ((t : ℕ) + 1 : ℕ) := by push_cast; ring
      rw [hcast]; exact this.symm
    · -- j + 1 ≠ p + t  ⟺  j ≠ p + t - 1
      intro h
      rcases (t : ℕ).eq_zero_or_pos with h0 | hpos
      · apply hjm1
        have hh : j + 1 = p := by simp only [h0, Nat.cast_zero, add_zero] at h; exact h
        rw [← hh]; ring
      · have hcast : p + (t : ℕ) = p + (((t : ℕ) - 1 : ℕ)) + 1 := by
          rw [Nat.cast_sub hpos]; push_cast; ring
        rw [hcast] at h
        have hjeq : j = p + (((t : ℕ) - 1 : ℕ)) := add_right_cancel h
        have hlt : (t : ℕ) - 1 < L + 1 := by omega
        have := hjrun ⟨(t : ℕ) - 1, hlt⟩
        simp only [] at this
        exact this hjeq
  -- per-pair separations
  have hsep : ∀ (t : Fin L) (j : ZMod P.n),
      (∀ s : Fin (L + 1), j ≠ p + (s : ℕ)) → j ≠ p - 1 →
      ∃ r > 0, ∀ x ∈ P.edgeSeg (p + (t : ℕ)), ∀ x' ∈ P.edgeSeg j, r ≤ dist x x' := by
    intro t j hjrun hjm1
    obtain ⟨h1, h2, h3⟩ := hnonadj t j hjrun hjm1
    exact edges_uniformly_separated P hsimple _ _ h1 h2 h3
  -- collect the bad edges into a finset and minimise over the finite product
  set Bad : Finset (ZMod P.n) := Finset.univ.filter
    (fun j => (∀ s : Fin (L + 1), j ≠ p + (s : ℕ)) ∧ j ≠ p - 1) with hBad
  set Pairs : Finset (Fin L × ZMod P.n) := Finset.univ ×ˢ Bad with hPairs
  -- choose a separation radius for each pair
  have hchoose : ∀ z ∈ Pairs, ∃ r > 0, ∀ x ∈ P.edgeSeg (p + ((z.1 : ℕ))),
      ∀ x' ∈ P.edgeSeg z.2, r ≤ dist x x' := by
    rintro ⟨t, j⟩ hz
    rw [hPairs, Finset.mem_product] at hz
    have hjB := hz.2; rw [hBad, Finset.mem_filter] at hjB
    exact hsep t j hjB.2.1 hjB.2.2
  choose! rr hrr hsepr using hchoose
  by_cases hPe : Pairs.Nonempty
  · refine ⟨Pairs.inf' hPe rr, (Finset.lt_inf'_iff _).mpr (fun z hz => hrr z hz), ?_⟩
    intro t j hjrun hjm1 x hx x' hx'
    have hjB : j ∈ Bad := by rw [hBad, Finset.mem_filter]; exact ⟨Finset.mem_univ j, hjrun, hjm1⟩
    have hzP : (t, j) ∈ Pairs := by rw [hPairs, Finset.mem_product]; exact ⟨Finset.mem_univ t, hjB⟩
    have hle : Pairs.inf' hPe rr ≤ rr (t, j) := Finset.inf'_le _ hzP
    exact le_trans hle (hsepr (t, j) hzP x hx x' hx')
  · -- no bad pairs (e.g. L = 0): vacuous
    refine ⟨1, one_pos, ?_⟩
    intro t j hjrun hjm1 x hx x' hx'
    refine absurd ⟨(t, j), ?_⟩ hPe
    rw [hPairs, Finset.mem_product]
    exact ⟨Finset.mem_univ t, by rw [hBad, Finset.mem_filter]; exact ⟨Finset.mem_univ j, hjrun, hjm1⟩⟩

/-- **Clearance strictly above a horizontal top run, near a run vertex.** Suppose all run
vertices `p, …, p+L` sit at the same height `w` (`hrun`), and the two end neighbours
`vert (p-1)`, `vert (p+L+1)` lie strictly below `w` (`hbelowL`, `hbelowR`). Then there is
`r > 0` such that for every run vertex `vp = vert (p + t)`, every point of the ball
`ball vp r` that lies strictly above `w` is off the boundary. Proof: by
`plateau_isolating_ball` the only edges meeting the ball are the run-incident ones
(`p-1, p, …, p+L`); every incident edge has both endpoints at height `≤ w` (run edges at
exactly `w`, the two end edges have one endpoint below `w`), so each lies entirely at
height `≤ w`; hence strictly above `w` the ball is boundary-free. -/
lemma plateau_clear_above_near_vertex (hsimple : P.IsSimple) (p : ZMod P.n) (L : ℕ)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowL : (toReal (P.vert (p - 1))).2 < w)
    (hbelowR : (toReal (P.vert (p + (L : ℕ) + 1))).2 < w) :
    ∃ r > 0, ∀ (t : Fin (L + 1)) (q : ℝ × ℝ),
      q ∈ Metric.ball (toReal (P.vert (p + (t : ℕ)))) r → w < q.2 → q ∉ P.boundary := by
  classical
  obtain ⟨r, hr, hiso⟩ := plateau_isolating_ball P hsimple p L
  refine ⟨r, hr, ?_⟩
  rintro t q hqball hqw ⟨_, ⟨j, rfl⟩, hqj⟩
  -- q is on edge j; if j is non-incident, the isolating ball excludes it
  -- so j must be a run-incident edge: p-1, or p + s for some s
  by_cases hjm1 : j = p - 1
  · -- entering edge: vert(p-1) → vert(p-1+1) = vert p at w; both heights ≤ w
    subst hjm1
    simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hqj
    obtain ⟨s, hs, hxy⟩ := hqj
    have e1 : (toReal (P.vert (p - 1 + 1))).2 = w := by
      have : p - 1 + 1 = p + ((0 : Fin (L + 1)) : ℕ) := by simp
      rw [this]; exact hrun 0
    have : q.2 ≤ w := by
      rw [← hxy]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [hs.1, hs.2, hbelowL, e1]
    linarith
  · by_cases hjrun : ∃ s : Fin (L + 1), j = p + (s : ℕ)
    · obtain ⟨s, rfl⟩ := hjrun
      -- run/leaving edge p+s : vert(p+s) → vert(p+s+1); both heights ≤ w
      simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hqj
      obtain ⟨u, hu, hxy⟩ := hqj
      have e0 : (toReal (P.vert (p + (s : ℕ)))).2 = w := hrun s
      have e1 : (toReal (P.vert (p + (s : ℕ) + 1))).2 ≤ w := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp s.isLt) with hslt | hseq
        · -- s + 1 ≤ L : still a run vertex
          have : p + (s : ℕ) + 1 = p + ((s : ℕ) + 1 : ℕ) := by push_cast; ring
          rw [this]
          have hlt : (s : ℕ) + 1 < L + 1 := by omega
          have := hrun ⟨(s : ℕ) + 1, hlt⟩
          simp only [] at this; rw [this]
        · -- s = L : leaving edge endpoint vert(p+L+1) strictly below w
          have hsv : (s : ℕ) = L := hseq
          have : p + (s : ℕ) + 1 = p + (L : ℕ) + 1 := by rw [hsv]
          rw [this]; exact hbelowR.le
      have : q.2 ≤ w := by
        rw [← hxy]
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        nlinarith [hu.1, hu.2, e0, e1]
      linarith
    · -- non-incident edge: excluded by the isolating ball
      push Not at hjrun
      exact absurd hqj (Set.disjoint_left.mp (hiso t j hjrun hjm1) hqball)

/-- **Discrete IVT coverage of a finite real chain.** For a sequence `f : Fin (L+1) → ℝ`
and any value `x` lying between two of its terms `f a ≤ x ≤ f b`, some consecutive pair
straddles `x`: there is `t : Fin L` with `x` between `f t.castSucc` and `f t.succ`. The
polyline through `f 0, …, f L` sweeps continuously, so by a discrete intermediate-value
argument every intermediate value is crossed by some edge of the chain. -/
lemma chain_covers_between {L : ℕ} (hL : 0 < L) (f : Fin (L + 1) → ℝ) (x : ℝ)
    (a b : Fin (L + 1)) (hax : f a ≤ x) (hxb : x ≤ f b) :
    ∃ t : Fin L, (f t.castSucc ≤ x ∧ x ≤ f t.succ) ∨ (f t.succ ≤ x ∧ x ≤ f t.castSucc) := by
  classical
  -- Consider the set of indices i with f i ≤ x; it is nonempty (contains a). Pick the
  -- largest index s with f s ≤ x. If s = L then f L ≤ x ≤ f b ≤ f L forces edge L-1.
  -- Otherwise f s ≤ x < f (s+1): edge s straddles.
  by_contra hcon
  rw [not_exists] at hcon
  -- hcon: every consecutive pair fails to straddle x
  -- Show by induction that the side of x is invariant along the chain, contradicting
  -- f a ≤ x ≤ f b with a, b possibly on different sides.
  have hstep : ∀ t : Fin L, (f t.castSucc ≤ x ↔ f t.succ ≤ x) := by
    intro t
    have h := hcon t
    rcases le_or_gt (f t.castSucc) x with h1 | h1 <;> rcases le_or_gt (f t.succ) x with h2 | h2
    · exact iff_of_true h1 h2
    · exact absurd (Or.inl ⟨h1, le_of_lt h2⟩) h
    · exact absurd (Or.inr ⟨h2, le_of_lt h1⟩) h
    · exact iff_of_false (not_le.mpr h1) (not_le.mpr h2)
  -- the predicate (f i ≤ x) is constant in i
  have hconst : ∀ i : Fin (L + 1), (f i ≤ x) ↔ (f 0 ≤ x) := by
    intro i
    obtain ⟨m, hm⟩ := i
    induction m with
    | zero => simp
    | succ k ih =>
      have hkL : k < L := by omega
      have hkL1 : k < L + 1 := by omega
      have e1 : (⟨k + 1, hm⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp
      have e2 : (⟨k, hkL1⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp
      rw [e1, ← hstep ⟨k, hkL⟩, ← e2]
      exact ih hkL1
  -- a, b give f a ≤ x and f b ≤ x ⟺ ... ; but if a and b straddle x strictly we contradict
  have ha0 : (f 0 ≤ x) := (hconst a).mp hax
  -- from hxb: x ≤ f b. If f b ≤ x too then f b = x; otherwise x < f b.
  rcases eq_or_lt_of_le hxb with hbeq | hblt
  · -- x = f b ; then b straddles with a, but need a consecutive pair. Use f 0.
    -- f 0 ≤ x = f b ; also f b ≤ x; so (f b ≤ x) true and constant ⟹ all ≤ x.
    -- Then take any t with f t.succ side. Actually we contradict via: x ≤ f all? no.
    -- Simpler: x = f b means b itself realises equality; pick adjacent edge to b.
    rcases (Nat.lt_or_ge (b : ℕ) L) with hbL | hbge
    · refine absurd ?_ (hcon ⟨(b:ℕ), hbL⟩)
      have hcseq : ((⟨(b:ℕ), hbL⟩ : Fin L).castSucc) = b := by apply Fin.ext; simp
      have hb1 : ((⟨(b:ℕ), hbL⟩ : Fin L).succ : Fin (L+1)) = ⟨(b:ℕ)+1, by omega⟩ := by
        apply Fin.ext; simp
      refine Or.inr ⟨?_, ?_⟩
      · rw [hb1]; exact (hconst ⟨(b:ℕ)+1, by omega⟩).mpr ha0
      · rw [hcseq]; exact hxb
    · -- b = L : x = f L, and f 0 ≤ x.  edge L-1 straddles
      have hbL : (b : ℕ) = L := by omega
      refine absurd ?_ (hcon ⟨L - 1, by omega⟩)
      have hsucc : ((⟨L-1, by omega⟩ : Fin L).succ : Fin (L+1)) = ⟨L, by omega⟩ := by
        apply Fin.ext; simp; omega
      have hcs : ((⟨L-1, by omega⟩ : Fin L).castSucc : Fin (L+1)) = ⟨L-1, by omega⟩ := by
        apply Fin.ext; simp
      refine Or.inl ⟨?_, ?_⟩
      · rw [hcs]; exact (hconst ⟨L-1, by omega⟩).mpr ha0
      · rw [hsucc]
        have hbb : (⟨L, by omega⟩ : Fin (L+1)) = b := by apply Fin.ext; simp [hbL]
        rw [hbb]; exact le_of_eq hbeq
  · -- x < f b : then ¬(f b ≤ x), but constancy says (f b ≤ x) ↔ (f 0 ≤ x) = true. Contradiction.
    exact absurd ((hconst b).mpr ha0) (not_le.mpr hblt)

/-- **Level-line clearance just left of the leftmost run vertex.** Let the run vertices
`p, …, p+L` all sit at height `w` (`hrun`), with end neighbours strictly below
(`hbelowL`, `hbelowR`). Suppose `mL : Fin (L+1)` is *x-leftmost* in the run: every run
vertex has abscissa `≥ (vert (p+mL)).1 =: xmin` (`hmin`). Then there is `ε > 0` such that
every point `(x, w)` with `xmin - ε < x < xmin` is off the boundary. Proof: by
`box_meets_only_incident_edges` at `p+mL`, any boundary point of the box around that vertex
lies on an incident edge `p+mL-1` or `p+mL`. The two incident edges each connect `p+mL`
(at `xmin`) to a vertex with abscissa `≥ xmin` (run neighbour) or strictly below height `w`
(end edge); in either case at height exactly `w` the edge has no point with abscissa
`< xmin`. So `x < xmin` is clear. -/
lemma plateau_level_clear_left (hsimple : P.IsSimple) (p : ZMod P.n) (L : ℕ)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowL : (toReal (P.vert (p - 1))).2 < w)
    (hbelowR : (toReal (P.vert (p + (L : ℕ) + 1))).2 < w)
    (mL : Fin (L + 1))
    (hmin : ∀ t : Fin (L + 1),
      (toReal (P.vert (p + (mL : ℕ)))).1 ≤ (toReal (P.vert (p + (t : ℕ)))).1) :
    ∃ ε > 0, ∀ x : ℝ,
      (toReal (P.vert (p + (mL : ℕ)))).1 - ε < x →
      x < (toReal (P.vert (p + (mL : ℕ)))).1 →
      ((x, w) : ℝ × ℝ) ∉ P.boundary := by
  classical
  set v := toReal (P.vert (p + (mL : ℕ))) with hv
  set xmin := v.1 with hxmin
  have hvw : v.2 = w := hrun mL
  obtain ⟨ε, hε, hbox⟩ := box_meets_only_incident_edges P hsimple (p + (mL : ℕ))
  refine ⟨ε, hε, ?_⟩
  intro x hx1 hx2 hxb
  -- (x, w) is in the box around v
  have hqbox : ((x, w) : ℝ × ℝ) ∈ Set.Ioo (v.1 - ε) (v.1 + ε) ×ˢ Set.Ioo (v.2 - ε) (v.2 + ε) := by
    refine ⟨⟨hx1, by linarith [hx2]⟩, ?_⟩
    rw [hvw]; exact ⟨by linarith [hε], by linarith [hε]⟩
  -- so (x,w) is on incident edge (p+mL)-1 or (p+mL); both have x-coord ≥ xmin at height w
  -- handle each incident edge: at height w, every point has abscissa ≥ xmin
  have hxge : xmin ≤ x := by
    rcases hbox (x, w) hqbox hxb with hc | hc
    · -- edge (p+mL)-1 : from vert((p+mL)-1) to vert((p+mL)) = v
      simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hc
      obtain ⟨s, hs, hxy⟩ := hc
      -- the upper endpoint is v (at height w); the lower endpoint:
      have htop : toReal (P.vert ((p + (mL : ℕ)) - 1 + 1)) = v := by
        have : (p + (mL : ℕ)) - 1 + 1 = p + (mL : ℕ) := by ring
        rw [this]
      -- lower endpoint abscissa ≥ xmin: it is either a run vertex or the entering vertex
      have hlow_x : xmin ≤ (toReal (P.vert ((p + (mL : ℕ)) - 1))).1 ∨
          (toReal (P.vert ((p + (mL : ℕ)) - 1))).2 < w := by
        rcases (mL : ℕ).eq_zero_or_pos with h0 | hpos
        · -- mL = 0 : (p+0)-1 = p-1, the entering vertex, strictly below w
          right
          have : (p + (mL : ℕ)) - 1 = p - 1 := by simp [h0]
          rw [this]; exact hbelowL
        · -- mL ≥ 1 : (p+mL)-1 = p + (mL-1), a run vertex, abscissa ≥ xmin
          left
          have hcast : (p + (mL : ℕ)) - 1 = p + ((mL : ℕ) - 1 : ℕ) := by
            rw [Nat.cast_sub hpos]; push_cast; ring
          rw [hcast]
          have := hmin ⟨(mL : ℕ) - 1, by omega⟩
          simpa only [Fin.val_mk] using this
      -- from the convex combination: x = (1-s) * low.1 + s * v.1, and the height equation
      -- forces s = 1 in the "low below w" case (lower endpoint strictly below w), else
      -- x ≥ min(low.1, xmin) = xmin
      rw [Prod.ext_iff] at hxy
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
      obtain ⟨hxeq, hyeq⟩ := hxy
      rw [htop] at hxeq hyeq
      rcases hlow_x with hlowx | hlowbelow
      · -- both endpoints abscissa ≥ xmin ⟹ convex combo ≥ xmin
        rw [← hxeq]; nlinarith [hs.1, hs.2, hlowx, le_refl xmin]
      · -- lower endpoint below w; height eq (1-s)*low.2 + s*w = w forces s = 1, x = v.1 = xmin
        rw [hvw] at hyeq
        have hprod : (1 - s) * (w - (toReal (P.vert ((p + (mL : ℕ)) - 1))).2) = 0 := by
          linear_combination -hyeq
        have hs1 : s = 1 := by
          by_contra hsne
          have hspos : 0 < 1 - s := by
            rcases lt_or_eq_of_le hs.2 with h | h
            · linarith
            · exact absurd h hsne
          have : 0 < (1 - s) * (w - (toReal (P.vert ((p + (mL : ℕ)) - 1))).2) :=
            mul_pos hspos (by linarith [hlowbelow])
          rw [hprod] at this; exact lt_irrefl _ this
        rw [hs1] at hxeq
        have : x = xmin := by rw [← hxeq, hxmin]; ring
        rw [this]
    · -- edge (p+mL) : from v to vert((p+mL)+1)
      simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hc
      obtain ⟨s, hs, hxy⟩ := hc
      have hhi_x : xmin ≤ (toReal (P.vert ((p + (mL : ℕ)) + 1))).1 ∨
          (toReal (P.vert ((p + (mL : ℕ)) + 1))).2 < w := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp mL.isLt) with hlt | heq
        · left
          have hcast : (p + (mL : ℕ)) + 1 = p + ((mL : ℕ) + 1 : ℕ) := by push_cast; ring
          rw [hcast]
          have := hmin ⟨(mL : ℕ) + 1, by omega⟩
          simpa only [Fin.val_mk] using this
        · right
          have hcast : (p + (mL : ℕ)) + 1 = p + (L : ℕ) + 1 := by rw [heq]
          rw [hcast]; exact hbelowR
      rw [Prod.ext_iff] at hxy
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
      obtain ⟨hxeq, hyeq⟩ := hxy
      rcases hhi_x with hhix | hhibelow
      · rw [← hxeq]; nlinarith [hs.1, hs.2, hhix, le_refl xmin]
      · rw [hvw] at hyeq
        have hprod : s * (w - (toReal (P.vert ((p + (mL : ℕ)) + 1))).2) = 0 := by
          linear_combination -hyeq
        have hs0 : s = 0 := by
          by_contra hsne
          have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsne)
          have : 0 < s * (w - (toReal (P.vert ((p + (mL : ℕ)) + 1))).2) :=
            mul_pos hspos (by linarith [hhibelow])
          rw [hprod] at this; exact lt_irrefl _ this
        rw [hs0] at hxeq
        have : x = xmin := by rw [← hxeq, hxmin]; ring
        rw [this]
  linarith

/-- **Level-line clearance just right of the rightmost run vertex.** Mirror of
`plateau_level_clear_left`: if `mR` is x-rightmost in the run (every run vertex has
abscissa `≤ (vert (p+mR)).1 =: xmax`), there is `ε > 0` with `(x, w)` off boundary for
every `xmax < x < xmax + ε`. -/
lemma plateau_level_clear_right (hsimple : P.IsSimple) (p : ZMod P.n) (L : ℕ)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowL : (toReal (P.vert (p - 1))).2 < w)
    (hbelowR : (toReal (P.vert (p + (L : ℕ) + 1))).2 < w)
    (mR : Fin (L + 1))
    (hmax : ∀ t : Fin (L + 1),
      (toReal (P.vert (p + (t : ℕ)))).1 ≤ (toReal (P.vert (p + (mR : ℕ)))).1) :
    ∃ ε > 0, ∀ x : ℝ,
      (toReal (P.vert (p + (mR : ℕ)))).1 < x →
      x < (toReal (P.vert (p + (mR : ℕ)))).1 + ε →
      ((x, w) : ℝ × ℝ) ∉ P.boundary := by
  classical
  set v := toReal (P.vert (p + (mR : ℕ))) with hv
  set xmax := v.1 with hxmax
  have hvw : v.2 = w := hrun mR
  obtain ⟨ε, hε, hbox⟩ := box_meets_only_incident_edges P hsimple (p + (mR : ℕ))
  refine ⟨ε, hε, ?_⟩
  intro x hx1 hx2 hxb
  have hqbox : ((x, w) : ℝ × ℝ) ∈ Set.Ioo (v.1 - ε) (v.1 + ε) ×ˢ Set.Ioo (v.2 - ε) (v.2 + ε) := by
    refine ⟨⟨by linarith [hx1], hx2⟩, ?_⟩
    rw [hvw]; exact ⟨by linarith [hε], by linarith [hε]⟩
  have hxle : x ≤ xmax := by
    rcases hbox (x, w) hqbox hxb with hc | hc
    · simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hc
      obtain ⟨s, hs, hxy⟩ := hc
      have htop : toReal (P.vert ((p + (mR : ℕ)) - 1 + 1)) = v := by
        have : (p + (mR : ℕ)) - 1 + 1 = p + (mR : ℕ) := by ring
        rw [this]
      have hlow : (toReal (P.vert ((p + (mR : ℕ)) - 1))).1 ≤ xmax ∨
          (toReal (P.vert ((p + (mR : ℕ)) - 1))).2 < w := by
        rcases (mR : ℕ).eq_zero_or_pos with h0 | hpos
        · right
          have : (p + (mR : ℕ)) - 1 = p - 1 := by simp [h0]
          rw [this]; exact hbelowL
        · left
          have hcast : (p + (mR : ℕ)) - 1 = p + ((mR : ℕ) - 1 : ℕ) := by
            rw [Nat.cast_sub hpos]; push_cast; ring
          rw [hcast]
          have := hmax ⟨(mR : ℕ) - 1, by omega⟩
          simpa only [Fin.val_mk] using this
      rw [Prod.ext_iff] at hxy
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
      obtain ⟨hxeq, hyeq⟩ := hxy
      rw [htop] at hxeq hyeq
      rcases hlow with hlowx | hlowbelow
      · rw [← hxeq]; nlinarith [hs.1, hs.2, hlowx, le_refl xmax]
      · rw [hvw] at hyeq
        have hprod : (1 - s) * (w - (toReal (P.vert ((p + (mR : ℕ)) - 1))).2) = 0 := by
          linear_combination -hyeq
        have hs1 : s = 1 := by
          by_contra hsne
          have hspos : 0 < 1 - s := by
            rcases lt_or_eq_of_le hs.2 with h | h
            · linarith
            · exact absurd h hsne
          have : 0 < (1 - s) * (w - (toReal (P.vert ((p + (mR : ℕ)) - 1))).2) :=
            mul_pos hspos (by linarith [hlowbelow])
          rw [hprod] at this; exact lt_irrefl _ this
        rw [hs1] at hxeq
        have : x = xmax := by rw [← hxeq, hxmax]; ring
        rw [this]
    · simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hc
      obtain ⟨s, hs, hxy⟩ := hc
      have hhi : (toReal (P.vert ((p + (mR : ℕ)) + 1))).1 ≤ xmax ∨
          (toReal (P.vert ((p + (mR : ℕ)) + 1))).2 < w := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp mR.isLt) with hlt | heq
        · left
          have hcast : (p + (mR : ℕ)) + 1 = p + ((mR : ℕ) + 1 : ℕ) := by push_cast; ring
          rw [hcast]
          have := hmax ⟨(mR : ℕ) + 1, by omega⟩
          simpa only [Fin.val_mk] using this
        · right
          have hcast : (p + (mR : ℕ)) + 1 = p + (L : ℕ) + 1 := by rw [heq]
          rw [hcast]; exact hbelowR
      rw [Prod.ext_iff] at hxy
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
      obtain ⟨hxeq, hyeq⟩ := hxy
      rcases hhi with hhix | hhibelow
      · rw [← hxeq]; nlinarith [hs.1, hs.2, hhix, le_refl xmax]
      · rw [hvw] at hyeq
        have hprod : s * (w - (toReal (P.vert ((p + (mR : ℕ)) + 1))).2) = 0 := by
          linear_combination -hyeq
        have hs0 : s = 0 := by
          by_contra hsne
          have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsne)
          have : 0 < s * (w - (toReal (P.vert ((p + (mR : ℕ)) + 1))).2) :=
            mul_pos hspos (by linarith [hhibelow])
          rw [hprod] at this; exact lt_irrefl _ this
        rw [hs0] at hxeq
        have : x = xmax := by rw [← hxeq, hxmax]; ring
        rw [this]
  linarith

/-- A point `(x, w)` lies on the horizontal segment between `(c, w)` and `(d, w)` whenever
`x` is between `c` and `d` (either order). -/
lemma mem_segment_horizontal (c d w x : ℝ)
    (hx : (c ≤ x ∧ x ≤ d) ∨ (d ≤ x ∧ x ≤ c)) :
    ((x, w) : ℝ × ℝ) ∈ segment ℝ ((c, w) : ℝ × ℝ) ((d, w) : ℝ × ℝ) := by
  have key : ∀ c d : ℝ, c ≤ x → x ≤ d →
      ((x, w) : ℝ × ℝ) ∈ segment ℝ ((c, w) : ℝ × ℝ) ((d, w) : ℝ × ℝ) := by
    intro c d hc hd
    rcases eq_or_lt_of_le (le_trans hc hd) with hcd | hcd
    · -- c = d, so x = c = d
      have : x = c := le_antisymm (hcd ▸ hd) hc
      subst this; rw [hcd]; exact left_mem_segment ℝ _ _
    · rw [segment_eq_image]
      refine ⟨(x - c) / (d - c), ⟨?_, ?_⟩, ?_⟩
      · apply div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
      · have hdc : d - c ≠ 0 := by linarith
        rw [Prod.ext_iff]
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; field_simp; ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key c d h1 h2
  · rw [segment_symm]; exact key d c h1 h2

/-- **The half-strip strictly above a horizontal top run is boundary-free.** Run vertices
`p, …, p+L` (`L ≥ 1`) all at height `w` (`hrun`); end neighbours `vert (p-1)`,
`vert (p+L+1)` strictly below `w` (`hbelowL`, `hbelowR`). Then there is `r > 0` such that
every point `(x, z)` with `x` in the run's `x`-range — i.e. `f a ≤ x ≤ f b` for the
endpoint abscissae `f i := (vert (p+i)).1` and some run indices `a, b` — and `w < z < w+r`
is off the boundary. Proof: `chain_covers_between` puts `(x, w)` on some run edge `p+t`
(horizontal at `w`); then `(x,z)` is within `z-w < r` of that run-edge point, so by
`plateau_seg_isolating_ball` it cannot lie on any non-run-incident edge, while every
run-incident edge sits at height `≤ w < z`. -/
lemma plateau_clear_above (hsimple : P.IsSimple) (p : ZMod P.n) (L : ℕ) (hL : 0 < L)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowL : (toReal (P.vert (p - 1))).2 < w)
    (hbelowR : (toReal (P.vert (p + (L : ℕ) + 1))).2 < w) :
    ∃ r > 0, ∀ (x z : ℝ) (a b : Fin (L + 1)),
      (toReal (P.vert (p + (a : ℕ)))).1 ≤ x → x ≤ (toReal (P.vert (p + (b : ℕ)))).1 →
      w < z → z < w + r → ((x, z) : ℝ × ℝ) ∉ P.boundary := by
  classical
  obtain ⟨r, hr, hseg⟩ := plateau_seg_isolating_ball P hsimple p L
  refine ⟨r, hr, ?_⟩
  rintro x z a b hax hxb hwz hzr hxb_mem
  -- (x, w) lies on some run edge p+t
  set f : Fin (L + 1) → ℝ := fun i => (toReal (P.vert (p + (i : ℕ)))).1 with hf
  obtain ⟨t, ht⟩ := chain_covers_between (L := L) hL f x a b hax hxb
  -- the run edge p+t straddles x in abscissa; the segment is horizontal at w, hence
  -- (x, w) is on edgeSeg (p+t)
  have hxw_mem : ((x, w) : ℝ × ℝ) ∈ P.edgeSeg (p + ((t : Fin L) : ℕ)) := by
    -- segment from (f t.castSucc, w) to (f t.succ, w): horizontal at w, x between endpoints
    have hep0 : toReal (P.vert (p + ((t : Fin L) : ℕ))) = (f t.castSucc, w) := by
      have : ((t : Fin L).castSucc : Fin (L+1)) = ⟨(t : ℕ), by omega⟩ := by apply Fin.ext; simp
      rw [Prod.ext_iff]; refine ⟨?_, hrun ⟨(t:ℕ), by omega⟩⟩
      simp only [hf, this]
    have hep1 : toReal (P.vert (p + ((t : Fin L) : ℕ) + 1)) = (f t.succ, w) := by
      have hcast : p + ((t : Fin L) : ℕ) + 1 = p + (((t : Fin L) : ℕ) + 1 : ℕ) := by
        push_cast; ring
      have hsv : ((t : Fin L).succ : Fin (L+1)) = ⟨(t:ℕ)+1, by omega⟩ := by apply Fin.ext; simp
      rw [hcast, Prod.ext_iff]
      refine ⟨?_, hrun ⟨(t:ℕ)+1, by omega⟩⟩
      simp only [hf, hsv]
    rw [LatticePolygon.edgeSeg, hep0, hep1]
    exact mem_segment_horizontal _ _ w x ht
  -- (x,z) ∈ boundary: on some edge j
  obtain ⟨_, ⟨j, rfl⟩, hqj⟩ := hxb_mem
  by_cases hjm1 : j = p - 1
  · subst hjm1
    simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hqj
    obtain ⟨s, hs, hxy⟩ := hqj
    have e1 : (toReal (P.vert (p - 1 + 1))).2 = w := by
      have : p - 1 + 1 = p + ((0 : Fin (L + 1)) : ℕ) := by simp
      rw [this]; exact hrun 0
    have : z ≤ w := by
      have : ((x, z) : ℝ × ℝ).2 ≤ w := by
        rw [← hxy]; simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        nlinarith [hs.1, hs.2, hbelowL, e1]
      simpa using this
    linarith
  · by_cases hjrun : ∃ s : Fin (L + 1), j = p + (s : ℕ)
    · obtain ⟨s, rfl⟩ := hjrun
      simp only [LatticePolygon.edgeSeg, segment_eq_image, Set.mem_image] at hqj
      obtain ⟨u, hu, hxy⟩ := hqj
      have e0 : (toReal (P.vert (p + (s : ℕ)))).2 = w := hrun s
      have e1 : (toReal (P.vert (p + (s : ℕ) + 1))).2 ≤ w := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp s.isLt) with hslt | hseq
        · have : p + (s : ℕ) + 1 = p + ((s : ℕ) + 1 : ℕ) := by push_cast; ring
          rw [this]
          have := hrun ⟨(s : ℕ) + 1, by omega⟩
          simp only [] at this; rw [this]
        · have hsv : (s : ℕ) = L := hseq
          have : p + (s : ℕ) + 1 = p + (L : ℕ) + 1 := by rw [hsv]
          rw [this]; exact hbelowR.le
      have : z ≤ w := by
        have : ((x, z) : ℝ × ℝ).2 ≤ w := by
          rw [← hxy]; simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          nlinarith [hu.1, hu.2, e0, e1]
        simpa using this
      linarith
    · -- non-incident edge: contradicts separation from run edge p+t containing (x,w)
      push Not at hjrun
      have hdist : r ≤ dist ((x, w) : ℝ × ℝ) ((x, z) : ℝ × ℝ) :=
        hseg t j hjrun hjm1 (x, w) hxw_mem (x, z) hqj
      have : dist ((x, w) : ℝ × ℝ) ((x, z) : ℝ × ℝ) < r := by
        rw [Prod.dist_eq]
        simp only [dist_self, Real.dist_eq]
        rw [max_lt_iff]
        exact ⟨by simpa using lt_of_le_of_lt (le_refl 0) hr, by
          rw [abs_lt]; constructor <;> [linarith; linarith]⟩
      linarith

/-- **At a strict local-max vertex, the level line through the apex is clear except at
the apex itself.** If `k` is a strict local maximum (`vert (k-1)` and `vert (k+1)` both
strictly below `w := (vert k).2`), there is `ε > 0` such that for every abscissa
`x ∈ (xv-ε, xv+ε)` with `x ≠ xv` (where `xv := (vert k).1`), the point `(x, w)` is off the
boundary. Proof: by `box_meets_only_incident_edges` any boundary point of the box lies on
the incident edge `k-1` or `k`; on each, the *only* point at height `w` is the apex itself
(the other endpoint is strictly below `w`), so `x = xv` — contradiction. -/
lemma apex_level_clear (hsimple : P.IsSimple) (k : ZMod P.n)
    (hkm1 : (toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2)
    (hkp1 : (toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2) :
    ∃ ε > 0, ∀ x : ℝ,
      x ∈ Set.Ioo ((toReal (P.vert k)).1 - ε) ((toReal (P.vert k)).1 + ε) →
      x ≠ (toReal (P.vert k)).1 →
      ((x, (toReal (P.vert k)).2) : ℝ × ℝ) ∉ P.boundary := by
  set v := toReal (P.vert k) with hv
  set w := v.2 with hw
  obtain ⟨ε, hε, hbox⟩ := box_meets_only_incident_edges P hsimple k
  refine ⟨ε, hε, ?_⟩
  rintro x ⟨hx1, hx2⟩ hxne hxb
  have hqbox : (x, w) ∈ Set.Ioo (v.1 - ε) (v.1 + ε) ×ˢ Set.Ioo (w - ε) (w + ε) :=
    ⟨⟨hx1, hx2⟩, ⟨by linarith, by linarith⟩⟩
  -- the shared endpoint of both incident edges is the apex v
  have e1 : (toReal (P.vert (k - 1 + 1))) = v := by
    have : k - 1 + 1 = k := by ring
    rw [this]
  have e1x : (toReal (P.vert (k - 1 + 1))).1 = v.1 := by rw [e1]
  have e1y : (toReal (P.vert (k - 1 + 1))).2 = w := by rw [e1]
  apply hxne
  rcases hbox (x, w) hqbox hxb with hc | hc
  · -- on edge (k-1): vert(k-1) → vert(k-1+1) = v.  Only the apex sits at height w.
    rw [LatticePolygon.edgeSeg, segment_eq_image] at hc
    obtain ⟨t, ht, hxy⟩ := hc
    rw [Prod.ext_iff] at hxy
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
    obtain ⟨hxeq, hyeq⟩ := hxy
    rw [e1y] at hyeq
    -- (1-t)*vert(k-1).2 + t*v.2 = w = v.2, with vert(k-1).2 < v.2 ⟹ t = 1
    have ht1 : t = 1 := by
      rcases eq_or_lt_of_le ht.2 with h | h
      · exact h
      · exfalso; nlinarith [hkm1, ht.1]
    rw [e1x, ht1] at hxeq
    rw [← hxeq]; ring
  · -- on edge k: v → vert(k+1).  Only the apex sits at height w.
    rw [LatticePolygon.edgeSeg, segment_eq_image] at hc
    obtain ⟨t, ht, hxy⟩ := hc
    rw [Prod.ext_iff] at hxy
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hxy
    obtain ⟨hxeq, hyeq⟩ := hxy
    have ht0 : t = 0 := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · exact h.symm
      · exfalso; nlinarith [hkp1, ht.2]
    rw [ht0] at hxeq
    rw [← hxeq]; ring

/-- **The two incident-edge thresholds localize at the apex abscissa.** At a strict
local-max vertex `k` with apex `v = (xv, w)`, both incident edges `k-1` (rising to the
apex) and `k` (descending from it) have crossing-threshold `→ xv` as the height `→ w`:
`edgeThr w (k-1) = edgeThr w k = xv` (`crossThreshold_top`/`crossThreshold_bot`), and both
are continuous in the height. Hence for any `ρ > 0` there is a two-sided neighbourhood
`(w-η, w+η)` on which both thresholds stay within `ρ` of `xv`. This is the analytic input
that lets the apex-cross choose flank columns strictly outside the closing "Λ". -/
lemma apex_thresholds_localize (k : ZMod P.n)
    (hdkm1 : (toReal (P.vert (k - 1))).2 ≠ (toReal (P.vert k)).2)
    (_hdk : (toReal (P.vert (k + 1))).2 ≠ (toReal (P.vert k)).2)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ η > 0, ∀ s, (toReal (P.vert k)).2 - η < s → s < (toReal (P.vert k)).2 + η →
      |P.edgeThr s (k - 1) - (toReal (P.vert k)).1| < ρ ∧
      |P.edgeThr s k - (toReal (P.vert k)).1| < ρ := by
  set v := toReal (P.vert k) with hv
  set w := v.2 with hw
  -- edge `k-1` goes `vert(k-1) → vert(k-1+1) = v`; its top-threshold is `v.1`.
  have e1 : (toReal (P.vert (k - 1 + 1))) = v := by
    have : k - 1 + 1 = k := by ring
    rw [this]
  have hval1 : P.edgeThr w (k - 1) = v.1 := by
    rw [LatticePolygon.edgeThr, e1]
    have : (toReal (P.vert (k - 1))).2 ≠ v.2 := hdkm1
    exact crossThreshold_top (toReal (P.vert (k - 1))) v this
  -- edge `k` goes `v → vert(k+1)`; its bottom-threshold (at height w = v.2) is `v.1`.
  have hval2 : P.edgeThr w k = v.1 := by
    rw [LatticePolygon.edgeThr]
    exact crossThreshold_bot v (toReal (P.vert (k + 1)))
  have hc1 : Continuous (fun s => P.edgeThr s (k - 1)) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hc2 : Continuous (fun s => P.edgeThr s k) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have h1 : ∀ᶠ s in nhds w, |P.edgeThr s (k - 1) - v.1| < ρ := by
    have := (hc1.continuousAt (x := w)).tendsto
    rw [hval1] at this
    exact (Metric.tendsto_nhds.mp this ρ hρ).mono (fun s hs => by rwa [Real.dist_eq] at hs)
  have h2 : ∀ᶠ s in nhds w, |P.edgeThr s k - v.1| < ρ := by
    have := (hc2.continuousAt (x := w)).tendsto
    rw [hval2] at this
    exact (Metric.tendsto_nhds.mp this ρ hρ).mono (fun s hs => by rwa [Real.dist_eq] at hs)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  refine ⟨η, hη, fun s hslo hshi => ?_⟩
  exact hball s (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)

/-- **The two run-incident edge thresholds localize at the run-end abscissae (plateau
form).** For a horizontal top run `p, …, p+L` (`L ≥ 1`) all at height `w`, with end
neighbours `vert (p-1)`, `vert (p+L+1)` strictly below `w`, the entering edge `p-1` (top
endpoint `vert p`) and the leaving edge `p+L` (bottom endpoint `vert (p+L)`) have crossing
thresholds tending to `(vert p).1` and `(vert (p+L)).1` respectively as the height tends to
`w`. Hence for any `ρ > 0` there is a one-sided neighbourhood `(w-η, w)` on which both stay
within `ρ` of those run-end abscissae. The plateau analog of `apex_thresholds_localize`. -/
lemma plateau_thresholds_localize (p : ZMod P.n) (L : ℕ)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowL : (toReal (P.vert (p - 1))).2 < w)
    (_hbelowR : (toReal (P.vert (p + (L : ℕ) + 1))).2 < w)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ η > 0, ∀ s, w - η < s → s < w + η →
      |P.edgeThr s (p - 1) - (toReal (P.vert p)).1| < ρ ∧
      |P.edgeThr s (p + (L : ℕ)) - (toReal (P.vert (p + (L : ℕ)))).1| < ρ := by
  classical
  -- entering edge `p-1` goes `vert(p-1) → vert(p-1+1) = vert p`; its top-threshold is `(vert p).1`.
  have e1 : (toReal (P.vert (p - 1 + 1))) = toReal (P.vert p) := by
    have : p - 1 + 1 = p := by ring
    rw [this]
  have hp_w : (toReal (P.vert p)).2 = w := by
    have := hrun 0; simpa using this
  have hval1 : P.edgeThr w (p - 1) = (toReal (P.vert p)).1 := by
    rw [LatticePolygon.edgeThr, e1, ← hp_w]
    exact crossThreshold_top (toReal (P.vert (p - 1))) (toReal (P.vert p)) (by
      rw [hp_w]; exact ne_of_lt hbelowL)
  -- leaving edge `p+L` goes `vert(p+L) → vert(p+L+1)`; its bottom-threshold (at w) is `(vert (p+L)).1`.
  have hpL_w : (toReal (P.vert (p + (L : ℕ)))).2 = w := hrun ⟨L, by omega⟩
  have hval2 : P.edgeThr w (p + (L : ℕ)) = (toReal (P.vert (p + (L : ℕ)))).1 := by
    rw [LatticePolygon.edgeThr]
    have := crossThreshold_bot (toReal (P.vert (p + (L : ℕ)))) (toReal (P.vert (p + (L : ℕ) + 1)))
    rw [hpL_w] at this; exact this
  have hc1 : Continuous (fun s => P.edgeThr s (p - 1)) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hc2 : Continuous (fun s => P.edgeThr s (p + (L : ℕ))) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have h1 : ∀ᶠ s in nhds w, |P.edgeThr s (p - 1) - (toReal (P.vert p)).1| < ρ := by
    have := (hc1.continuousAt (x := w)).tendsto
    rw [hval1] at this
    exact (Metric.tendsto_nhds.mp this ρ hρ).mono (fun s hs => by rwa [Real.dist_eq] at hs)
  have h2 : ∀ᶠ s in nhds w, |P.edgeThr s (p + (L : ℕ)) - (toReal (P.vert (p + (L : ℕ)))).1| < ρ := by
    have := (hc2.continuousAt (x := w)).tendsto
    rw [hval2] at this
    exact (Metric.tendsto_nhds.mp this ρ hρ).mono (fun s hs => by rwa [Real.dist_eq] at hs)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  refine ⟨η, hη, fun s hslo hshi => ?_⟩
  exact hball s (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)

/-- **An outer chord left of the entering edge stays strictly left of the entering
abscissa at the run level (plateau form).** For a top run `p, …, p+L` at height `w`, the
entering edge `p-1` rises to `vert p` (`edgeThr w (p-1) = (vert p).1`). If `eL` is an edge
non-incident to the entering vertex `p` (`eL ≠ p`, `eL ≠ p-1`), spans a generic `y < w` of
the vertex-free slab `(y, w)`, and lies strictly left of the entering edge at `y`, then
`edgeThr w eL < (vert p).1`. The plateau analog of `edgeThr_lt_apex_of_outer`. -/
lemma plateau_edgeThr_lt_enter_of_outer (hsimple : P.IsSimple) (p eL : ZMod P.n) (L : ℕ)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowL : (toReal (P.vert (p - 1))).2 < w)
    (heLp : eL ≠ p) (heLp1 : eL ≠ p - 1)
    (y : ℝ) (hyw : y < w)
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w))
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (heL_span : eL ∈ P.spanningSet y)
    (heL_span_w : eL ∈ P.spanningSet w)
    (hord : P.edgeThr y eL < P.edgeThr y (p - 1)) :
    P.edgeThr w eL < (toReal (P.vert p)).1 := by
  classical
  have hp_w : (toReal (P.vert p)).2 = w := by have := hrun 0; simpa using this
  -- the entering edge `p-1` spans `y` (lower endpoint `vert(p-1)`, upper `vert p`)
  have e1 : (toReal (P.vert (p - 1 + 1))) = toReal (P.vert p) := by
    have : p - 1 + 1 = p := by ring
    rw [this]
  have hpm1_lt_y : (toReal (P.vert (p - 1))).2 < y := by
    rcases lt_trichotomy (toReal (P.vert (p - 1))).2 y with h | h | h
    · exact h
    · exact absurd h (hygen (p - 1))
    · exact absurd ⟨h, by rw [hp_w] at *; exact hbelowL⟩ (hslab (p - 1))
  have hpm1_span : (p - 1) ∈ P.spanningSet y := by
    simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨hpm1_lt_y, by rw [e1, hp_w]; exact hyw⟩
  have hval1 : P.edgeThr w (p - 1) = (toReal (P.vert p)).1 := by
    rw [LatticePolygon.edgeThr, e1, ← hp_w]
    exact crossThreshold_top (toReal (P.vert (p - 1))) (toReal (P.vert p)) (by
      rw [hp_w]; exact ne_of_lt hbelowL)
  obtain ⟨y₀, hy₀y, hslab0⟩ := exists_vertexFree_slab_below P y w hygen hslab
  have hslabM : ∀ i, ¬ (y₀ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w) := hslab0
  have hc_eL : Continuous (fun s => P.edgeThr s eL) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hc_pm1 : Continuous (fun s => P.edgeThr s (p - 1)) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hyle : P.edgeThr w eL ≤ (toReal (P.vert p)).1 := by
    rw [← hval1]
    have hkey : ∀ z ∈ Set.Ioo y w, P.edgeThr z eL < P.edgeThr z (p - 1) := by
      intro z hz
      have hzM : z ∈ Set.Ioo y₀ w := ⟨lt_trans hy₀y hz.1, hz.2⟩
      have hyM : y ∈ Set.Ioo y₀ w := ⟨hy₀y, hyw⟩
      exact chord_order_preserved_in_slab P hsimple y₀ w hslabM eL (p - 1) hyM
        heL_span hpm1_span hord hzM
    have hL : Filter.Tendsto (fun z => P.edgeThr z eL) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w eL)) := (hc_eL.continuousAt).continuousWithinAt
    have hR : Filter.Tendsto (fun z => P.edgeThr z (p - 1)) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w (p - 1))) := (hc_pm1.continuousAt).continuousWithinAt
    have hne : (nhdsWithin w (Set.Iio w)).NeBot := nhdsLT_neBot_of_exists_lt ⟨y, hyw⟩
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds hyw)] with z hzlt hzgt
    exact (hkey z ⟨hzgt, hzlt⟩).le
  rcases lt_or_eq_of_le hyle with hlt | heq
  · exact hlt
  · exfalso
    have heL_span_w' : (((toReal (P.vert eL)).2 < w ∧ w < (toReal (P.vert (eL + 1))).2) ∨
        ((toReal (P.vert (eL + 1))).2 < w ∧ w < (toReal (P.vert eL)).2)) := by
      simpa [LatticePolygon.spanningSet, Finset.mem_filter] using heL_span_w
    have hmem : (P.edgeThr w eL, w) ∈ P.edgeSeg eL := by
      rw [LatticePolygon.edgeThr, LatticePolygon.edgeSeg]
      rcases heL_span_w' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact crossThreshold_mem_segment _ _ w h1 h2
      · exact crossThreshold_mem_segment_down _ _ w h1 h2
    rw [heq] at hmem
    have hvp : toReal (P.vert p) ∈ P.edgeSeg eL := by
      have hpe : ((toReal (P.vert p)).1, w) = toReal (P.vert p) := by
        rw [Prod.ext_iff]; exact ⟨rfl, hp_w.symm⟩
      rwa [hpe] at hmem
    exact vert_notMem_edgeSeg P hsimple p eL heLp heLp1 hvp

/-- **An outer chord right of the leaving edge stays strictly right of the leaving
abscissa at the run level (plateau form).** Mirror of `plateau_edgeThr_lt_enter_of_outer`:
the leaving edge `p+L` descends from `vert (p+L)` (`edgeThr w (p+L) = (vert (p+L)).1`); an
edge `eR` non-incident to the leaving vertex `p+L` (`eR ≠ p+L`, `eR ≠ p+L-1`) spanning a
generic `y < w` and lying strictly right of the leaving edge at `y` satisfies
`(vert (p+L)).1 < edgeThr w eR`. -/
lemma plateau_leave_lt_edgeThr_of_outer (hsimple : P.IsSimple) (p eR : ZMod P.n) (L : ℕ)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowR : (toReal (P.vert (p + (L : ℕ) + 1))).2 < w)
    (heRpL : eR ≠ p + (L : ℕ)) (heRpL1 : eR ≠ p + (L : ℕ) - 1)
    (y : ℝ) (hyw : y < w)
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w))
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (heR_span : eR ∈ P.spanningSet y)
    (heR_span_w : eR ∈ P.spanningSet w)
    (hord : P.edgeThr y (p + (L : ℕ)) < P.edgeThr y eR) :
    (toReal (P.vert (p + (L : ℕ)))).1 < P.edgeThr w eR := by
  classical
  have hpL_w : (toReal (P.vert (p + (L : ℕ)))).2 = w := hrun ⟨L, by omega⟩
  -- leaving edge `p+L` spans `y` (upper endpoint `vert (p+L)`, lower `vert(p+L+1)`)
  have hpL1_lt_y : (toReal (P.vert (p + (L : ℕ) + 1))).2 < y := by
    rcases lt_trichotomy (toReal (P.vert (p + (L : ℕ) + 1))).2 y with h | h | h
    · exact h
    · exact absurd h (hygen (p + (L : ℕ) + 1))
    · exact absurd ⟨h, hbelowR⟩ (hslab (p + (L : ℕ) + 1))
  have hpL_span : (p + (L : ℕ)) ∈ P.spanningSet y := by
    simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨hpL1_lt_y, by rw [hpL_w]; exact hyw⟩
  have hval2 : P.edgeThr w (p + (L : ℕ)) = (toReal (P.vert (p + (L : ℕ)))).1 := by
    rw [LatticePolygon.edgeThr]
    have := crossThreshold_bot (toReal (P.vert (p + (L : ℕ)))) (toReal (P.vert (p + (L : ℕ) + 1)))
    rw [hpL_w] at this; exact this
  obtain ⟨y₀, hy₀y, hslab0⟩ := exists_vertexFree_slab_below P y w hygen hslab
  have hslabM : ∀ i, ¬ (y₀ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w) := hslab0
  have hc_eR : Continuous (fun s => P.edgeThr s eR) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hc_pL : Continuous (fun s => P.edgeThr s (p + (L : ℕ))) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hyle : (toReal (P.vert (p + (L : ℕ)))).1 ≤ P.edgeThr w eR := by
    rw [← hval2]
    have hkey : ∀ z ∈ Set.Ioo y w, P.edgeThr z (p + (L : ℕ)) < P.edgeThr z eR := by
      intro z hz
      have hzM : z ∈ Set.Ioo y₀ w := ⟨lt_trans hy₀y hz.1, hz.2⟩
      have hyM : y ∈ Set.Ioo y₀ w := ⟨hy₀y, hyw⟩
      exact chord_order_preserved_in_slab P hsimple y₀ w hslabM (p + (L : ℕ)) eR hyM
        hpL_span heR_span hord hzM
    have hL : Filter.Tendsto (fun z => P.edgeThr z (p + (L : ℕ))) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w (p + (L : ℕ)))) := (hc_pL.continuousAt).continuousWithinAt
    have hR : Filter.Tendsto (fun z => P.edgeThr z eR) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w eR)) := (hc_eR.continuousAt).continuousWithinAt
    have hne : (nhdsWithin w (Set.Iio w)).NeBot := nhdsLT_neBot_of_exists_lt ⟨y, hyw⟩
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds hyw)] with z hzlt hzgt
    exact (hkey z ⟨hzgt, hzlt⟩).le
  rcases lt_or_eq_of_le hyle with hlt | heq
  · exact hlt
  · exfalso
    have heR_span_w' : (((toReal (P.vert eR)).2 < w ∧ w < (toReal (P.vert (eR + 1))).2) ∨
        ((toReal (P.vert (eR + 1))).2 < w ∧ w < (toReal (P.vert eR)).2)) := by
      simpa [LatticePolygon.spanningSet, Finset.mem_filter] using heR_span_w
    have hmem : (P.edgeThr w eR, w) ∈ P.edgeSeg eR := by
      rw [LatticePolygon.edgeThr, LatticePolygon.edgeSeg]
      rcases heR_span_w' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact crossThreshold_mem_segment _ _ w h1 h2
      · exact crossThreshold_mem_segment_down _ _ w h1 h2
    rw [← heq] at hmem
    have hvpL : toReal (P.vert (p + (L : ℕ))) ∈ P.edgeSeg eR := by
      have hpe : ((toReal (P.vert (p + (L : ℕ)))).1, w) = toReal (P.vert (p + (L : ℕ))) := by
        rw [Prod.ext_iff]; exact ⟨rfl, hpL_w.symm⟩
      rwa [hpe] at hmem
    exact vert_notMem_edgeSeg P hsimple (p + (L : ℕ)) eR heRpL heRpL1 hvpL

/-- **A non-run-incident edge's threshold avoids the run's x-range at the run level.**
For a top run `p, …, p+L` (`L ≥ 1`) at height `w`, let `e` be an edge non-incident to the
run (`e ≠ p-1` and `e ≠ p+s` for all `s`) that spans `w`. Then its crossing abscissa
`edgeThr w e` does not lie in the closed x-range `[xmin, xmax]` of the run vertices (here
`xmin = (vert (p+mL)).1`, `xmax = (vert (p+mR)).1` for x-extreme run indices). Proof: if it
did, `chain_covers_between` puts `(edgeThr w e, w)` on some run edge `p+t`; but it is also
on `edgeSeg e`, so the two non-adjacent edges share a point, contradicting simplicity. -/
lemma plateau_outer_thr_notMem_run_range (hsimple : P.IsSimple) (p e : ZMod P.n) (L : ℕ)
    (hL : 0 < L) (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (herun : ∀ s : Fin (L + 1), e ≠ p + (s : ℕ)) (hem1 : e ≠ p - 1)
    (he_span_w : e ∈ P.spanningSet w)
    (mL mR : Fin (L + 1)) :
    ¬ ((toReal (P.vert (p + (mL : ℕ)))).1 ≤ P.edgeThr w e ∧
        P.edgeThr w e ≤ (toReal (P.vert (p + (mR : ℕ)))).1) := by
  classical
  rintro ⟨hge, hle⟩
  set c := P.edgeThr w e with hc
  -- (c, w) lies on edgeSeg e
  have he_span_w' : (((toReal (P.vert e)).2 < w ∧ w < (toReal (P.vert (e + 1))).2) ∨
      ((toReal (P.vert (e + 1))).2 < w ∧ w < (toReal (P.vert e)).2)) := by
    simpa [LatticePolygon.spanningSet, Finset.mem_filter] using he_span_w
  have hmem_e : ((c, w) : ℝ × ℝ) ∈ P.edgeSeg e := by
    rw [hc, LatticePolygon.edgeThr, LatticePolygon.edgeSeg]
    rcases he_span_w' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact crossThreshold_mem_segment _ _ w h1 h2
    · exact crossThreshold_mem_segment_down _ _ w h1 h2
  -- (c, w) lies on some run edge p+t (chain_covers_between with a = mL, b = mR)
  set f : Fin (L + 1) → ℝ := fun i => (toReal (P.vert (p + (i : ℕ)))).1 with hf
  obtain ⟨t, ht⟩ := chain_covers_between (L := L) hL f c mL mR hge hle
  have hxw_mem : ((c, w) : ℝ × ℝ) ∈ P.edgeSeg (p + ((t : Fin L) : ℕ)) := by
    have hep0 : toReal (P.vert (p + ((t : Fin L) : ℕ))) = (f t.castSucc, w) := by
      have : ((t : Fin L).castSucc : Fin (L+1)) = ⟨(t : ℕ), by omega⟩ := by apply Fin.ext; simp
      rw [Prod.ext_iff]; refine ⟨?_, hrun ⟨(t:ℕ), by omega⟩⟩
      simp only [hf, this]
    have hep1 : toReal (P.vert (p + ((t : Fin L) : ℕ) + 1)) = (f t.succ, w) := by
      have hcast : p + ((t : Fin L) : ℕ) + 1 = p + (((t : Fin L) : ℕ) + 1 : ℕ) := by
        push_cast; ring
      have hsv : ((t : Fin L).succ : Fin (L+1)) = ⟨(t:ℕ)+1, by omega⟩ := by apply Fin.ext; simp
      rw [hcast, Prod.ext_iff]
      refine ⟨?_, hrun ⟨(t:ℕ)+1, by omega⟩⟩
      simp only [hf, hsv]
    rw [LatticePolygon.edgeSeg, hep0, hep1]
    exact mem_segment_horizontal _ _ w c ht
  -- e and the run edge p+t are non-adjacent ⟹ disjoint, contradicting shared (c,w)
  have hrunidx : (p + ((t : Fin L) : ℕ)) ≠ e ∧ (p + ((t : Fin L) : ℕ)) + 1 ≠ e ∧
      e + 1 ≠ (p + ((t : Fin L) : ℕ)) := by
    have htL1 : ((t : Fin L) : ℕ) < L + 1 := by omega
    have ht1L1 : ((t : Fin L) : ℕ) + 1 < L + 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · have := herun ⟨((t : Fin L) : ℕ), htL1⟩; simp only [] at this; exact this.symm
    · have := herun ⟨((t : Fin L) : ℕ) + 1, ht1L1⟩; simp only [] at this
      have hcast : p + ((t : Fin L) : ℕ) + 1 = p + (((t : Fin L) : ℕ) + 1 : ℕ) := by push_cast; ring
      rw [hcast]; exact this.symm
    · intro h
      rcases ((t : Fin L) : ℕ).eq_zero_or_pos with h0 | hpos
      · apply hem1
        have hh : e + 1 = p := by simp only [h0, Nat.cast_zero, add_zero] at h; exact h
        rw [← hh]; ring
      · have hcast : p + ((t : Fin L) : ℕ) = p + ((((t : Fin L) : ℕ) - 1 : ℕ)) + 1 := by
          rw [Nat.cast_sub hpos]; push_cast; ring
        rw [hcast] at h
        have heeq : e = p + ((((t : Fin L) : ℕ) - 1 : ℕ)) := add_right_cancel h
        have hlt : ((t : Fin L) : ℕ) - 1 < L + 1 := by omega
        have := herun ⟨((t : Fin L) : ℕ) - 1, hlt⟩
        simp only [] at this
        exact this heeq
  have hdisj : Disjoint (P.edgeSeg (p + ((t : Fin L) : ℕ))) (P.edgeSeg e) :=
    hsimple.2.1 _ _ hrunidx.1 hrunidx.2.1 hrunidx.2.2
  exact Set.disjoint_left.mp hdisj hxw_mem hmem_e

/-- **The left outer chord crosses strictly left of the run's `xmin` at the run level.**
Combining `plateau_edgeThr_lt_enter_of_outer` (giving `edgeThr w eL ≤ (vert p).1 ≤ xmax`)
with `plateau_outer_thr_notMem_run_range` (the threshold avoids `[xmin, xmax]`): the only
remaining possibility is `edgeThr w eL < xmin`. This is the precise placement fact letting
the plateau-cross set its left column at `xmin - ρ` strictly inside the left gap. -/
lemma plateau_outer_lt_xmin (hsimple : P.IsSimple) (p eL : ZMod P.n) (L : ℕ) (hL : 0 < L)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowL : (toReal (P.vert (p - 1))).2 < w)
    (heLrun : ∀ s : Fin (L + 1), eL ≠ p + (s : ℕ)) (heLm1 : eL ≠ p - 1)
    (y : ℝ) (hyw : y < w)
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w))
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (heL_span : eL ∈ P.spanningSet y) (heL_span_w : eL ∈ P.spanningSet w)
    (hord : P.edgeThr y eL < P.edgeThr y (p - 1))
    (mL mR : Fin (L + 1))
    (_hmin : ∀ t : Fin (L + 1),
      (toReal (P.vert (p + (mL : ℕ)))).1 ≤ (toReal (P.vert (p + (t : ℕ)))).1)
    (hmax : ∀ t : Fin (L + 1),
      (toReal (P.vert (p + (t : ℕ)))).1 ≤ (toReal (P.vert (p + (mR : ℕ)))).1) :
    P.edgeThr w eL < (toReal (P.vert (p + (mL : ℕ)))).1 := by
  -- eL is not incident to the entering vertex p (it is non-run-incident and ≠ p-1)
  have heLp : eL ≠ p := by have := heLrun 0; simpa using this
  have hlt_enter : P.edgeThr w eL < (toReal (P.vert p)).1 :=
    plateau_edgeThr_lt_enter_of_outer P hsimple p eL L w hrun hbelowL heLp heLm1 y hyw
      hslab hygen heL_span heL_span_w hord
  -- (vert p).1 ≤ xmax (p is a run vertex; mR is x-rightmost)
  have hp_le_xmax : (toReal (P.vert p)).1 ≤ (toReal (P.vert (p + (mR : ℕ)))).1 := by
    have := hmax 0; simpa using this
  have hnot := plateau_outer_thr_notMem_run_range P hsimple p eL L hL w hrun heLrun heLm1
    heL_span_w mL mR
  rw [not_and_or, not_le, not_le] at hnot
  rcases hnot with h | h
  · exact h
  · exact absurd (lt_of_lt_of_le hlt_enter hp_le_xmax) (not_lt.mpr h.le)

/-- **The right outer chord crosses strictly right of the run's `xmax` at the run level.**
Mirror of `plateau_outer_lt_xmin`: combining `plateau_leave_lt_edgeThr_of_outer`
(`xmin ≤ (vert (p+L)).1 ≤ edgeThr w eR`) with the avoidance of `[xmin, xmax]`, the only
possibility is `xmax < edgeThr w eR`. -/
lemma plateau_outer_gt_xmax (hsimple : P.IsSimple) (p eR : ZMod P.n) (L : ℕ) (hL : 0 < L)
    (w : ℝ)
    (hrun : ∀ t : Fin (L + 1), (toReal (P.vert (p + (t : ℕ)))).2 = w)
    (hbelowR : (toReal (P.vert (p + (L : ℕ) + 1))).2 < w)
    (heRrun : ∀ s : Fin (L + 1), eR ≠ p + (s : ℕ)) (heRm1 : eR ≠ p - 1)
    (y : ℝ) (hyw : y < w)
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w))
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (heR_span : eR ∈ P.spanningSet y) (heR_span_w : eR ∈ P.spanningSet w)
    (hord : P.edgeThr y (p + (L : ℕ)) < P.edgeThr y eR)
    (mL mR : Fin (L + 1))
    (hmin : ∀ t : Fin (L + 1),
      (toReal (P.vert (p + (mL : ℕ)))).1 ≤ (toReal (P.vert (p + (t : ℕ)))).1)
    (_hmax : ∀ t : Fin (L + 1),
      (toReal (P.vert (p + (t : ℕ)))).1 ≤ (toReal (P.vert (p + (mR : ℕ)))).1) :
    (toReal (P.vert (p + (mR : ℕ)))).1 < P.edgeThr w eR := by
  have heRpL : eR ≠ p + (L : ℕ) := heRrun ⟨L, by omega⟩
  have heRpL1 : eR ≠ p + (L : ℕ) - 1 := by
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · omega
    · have hcast : p + (L : ℕ) - 1 = p + ((L - 1 : ℕ)) := by
        rw [Nat.cast_sub hLpos]; push_cast; ring
      rw [hcast]; exact heRrun ⟨L - 1, by omega⟩
  have hgt_leave : (toReal (P.vert (p + (L : ℕ)))).1 < P.edgeThr w eR :=
    plateau_leave_lt_edgeThr_of_outer P hsimple p eR L w hrun hbelowR heRpL heRpL1 y hyw
      hslab hygen heR_span heR_span_w hord
  have hxmin_le_pL : (toReal (P.vert (p + (mL : ℕ)))).1 ≤ (toReal (P.vert (p + (L : ℕ)))).1 :=
    hmin ⟨L, by omega⟩
  have hnot := plateau_outer_thr_notMem_run_range P hsimple p eR L hL w hrun heRrun heRm1
    heR_span_w mL mR
  rw [not_and_or, not_le, not_le] at hnot
  rcases hnot with h | h
  · exact absurd (lt_of_le_of_lt hxmin_le_pL hgt_leave) (not_lt.mpr h.le)
  · exact h

/-- **An outer chord flanking the apex stays strictly left of the apex abscissa at the
apex level.** At a strict local-max vertex `k` with apex `v = (xv, w)`, suppose `eL` is an
edge non-incident to `k` (`eL ≠ k`, `eL ≠ k-1`), spanning a generic height `y < w` of the
vertex-free slab `(y, w)`, and lying strictly left of the rising incident edge `k-1` at
`y` (`edgeThr y eL < edgeThr y (k-1)`). Then `edgeThr w eL < xv`. Proof: chord order is
preserved across the slab, so by continuity `edgeThr w eL ≤ edgeThr w (k-1) = xv`; and
`(edgeThr w eL, w) ∈ edgeSeg eL` while `(xv, w) = v ∉ edgeSeg eL` (`vert_notMem_edgeSeg`),
so the inequality is strict. -/
lemma edgeThr_lt_apex_of_outer (hsimple : P.IsSimple) (k eL : ZMod P.n)
    (hkm1 : (toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2)
    (heLk : eL ≠ k) (heLk1 : eL ≠ k - 1)
    (y : ℝ) (hyw : y < (toReal (P.vert k)).2)
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < (toReal (P.vert k)).2))
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (heL_span : eL ∈ P.spanningSet y)
    (heL_span_w : eL ∈ P.spanningSet (toReal (P.vert k)).2)
    (hord : P.edgeThr y eL < P.edgeThr y (k - 1)) :
    P.edgeThr (toReal (P.vert k)).2 eL < (toReal (P.vert k)).1 := by
  classical
  set v := toReal (P.vert k) with hv
  set w := v.2 with hw
  -- the rising incident edge `k-1` spans `y` (lower endpoint `vert(k-1)`, upper `vert k = v`)
  have e1 : (toReal (P.vert (k - 1 + 1))) = v := by
    have : k - 1 + 1 = k := by ring
    rw [this]
  have e1y : (toReal (P.vert (k - 1 + 1))).2 = w := by rw [e1]
  have hkm1_lt_y : (toReal (P.vert (k - 1))).2 < y := by
    rcases lt_trichotomy (toReal (P.vert (k - 1))).2 y with h | h | h
    · exact h
    · exact absurd h (hygen (k - 1))
    · exact absurd ⟨h, hkm1⟩ (hslab (k - 1))
  have hkm1_span : (k - 1) ∈ P.spanningSet y := by
    simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨hkm1_lt_y, by rw [e1y]; exact hyw⟩
  -- edgeThr w (k-1) = xv  (top of the rising edge)
  have hval1 : P.edgeThr w (k - 1) = v.1 := by
    rw [LatticePolygon.edgeThr, e1]
    exact crossThreshold_top (toReal (P.vert (k - 1))) v (by
      rw [show v.2 = w from rfl]; exact ne_of_lt hkm1)
  -- extend the slab below y so that y is strictly interior.
  obtain ⟨y₀, hy₀y, hslab0⟩ := exists_vertexFree_slab_below P y w hygen hslab
  have hslabM : ∀ i, ¬ (y₀ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w) := hslab0
  -- continuity of the two thresholds
  have hc_eL : Continuous (fun s => P.edgeThr s eL) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hc_km1 : Continuous (fun s => P.edgeThr s (k - 1)) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  -- ≤ at w via le_of_tendsto over heights approaching w from below within the slab
  have hyle : P.edgeThr w eL ≤ v.1 := by
    rw [← hval1]
    have hkey : ∀ z ∈ Set.Ioo y w, P.edgeThr z eL < P.edgeThr z (k - 1) := by
      intro z hz
      have hzM : z ∈ Set.Ioo y₀ w := ⟨lt_trans hy₀y hz.1, hz.2⟩
      have hyM : y ∈ Set.Ioo y₀ w := ⟨hy₀y, hyw⟩
      exact chord_order_preserved_in_slab P hsimple y₀ w hslabM eL (k - 1) hyM
        heL_span hkm1_span hord hzM
    have hL : Filter.Tendsto (fun z => P.edgeThr z eL) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w eL)) := (hc_eL.continuousAt).continuousWithinAt
    have hR : Filter.Tendsto (fun z => P.edgeThr z (k - 1)) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w (k - 1))) := (hc_km1.continuousAt).continuousWithinAt
    have hne : (nhdsWithin w (Set.Iio w)).NeBot := nhdsLT_neBot_of_exists_lt ⟨y, hyw⟩
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds hyw)] with z hzlt hzgt
    exact (hkey z ⟨hzgt, hzlt⟩).le
  -- strict: (edgeThr w eL, w) ∈ edgeSeg eL but v = (xv, w) ∉ edgeSeg eL
  rcases lt_or_eq_of_le hyle with hlt | heq
  · exact hlt
  · exfalso
    have heL_span_w' : (((toReal (P.vert eL)).2 < w ∧ w < (toReal (P.vert (eL + 1))).2) ∨
        ((toReal (P.vert (eL + 1))).2 < w ∧ w < (toReal (P.vert eL)).2)) := by
      simpa [LatticePolygon.spanningSet, Finset.mem_filter] using heL_span_w
    have hmem : (P.edgeThr w eL, w) ∈ P.edgeSeg eL := by
      rw [LatticePolygon.edgeThr, LatticePolygon.edgeSeg]
      rcases heL_span_w' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact crossThreshold_mem_segment _ _ w h1 h2
      · exact crossThreshold_mem_segment_down _ _ w h1 h2
    rw [heq] at hmem
    have : v ∈ P.edgeSeg eL := by
      have : (v.1, w) = v := by rw [Prod.ext_iff]; exact ⟨rfl, rfl⟩
      rwa [this] at hmem
    exact vert_notMem_edgeSeg P hsimple k eL heLk heLk1 this

/-- **Mirror of `edgeThr_lt_apex_of_outer` for the right flank.** At a strict local-max
vertex `k` with apex `v = (xv, w)`, an edge `eR` non-incident to `k` (`eR ≠ k`,
`eR ≠ k-1`) spanning a generic `y < w` of the vertex-free slab `(y, w)` and lying strictly
right of the *descending* incident edge `k` at `y` (`edgeThr y k < edgeThr y eR`), satisfies
`xv < edgeThr w eR`. Same proof comparing against edge `k` (whose bottom-threshold at `w` is
`xv`, via `crossThreshold_bot`). -/
lemma apex_lt_edgeThr_of_outer (hsimple : P.IsSimple) (k eR : ZMod P.n)
    (hkp1 : (toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2)
    (heRk : eR ≠ k) (heRk1 : eR ≠ k - 1)
    (y : ℝ) (hyw : y < (toReal (P.vert k)).2)
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < (toReal (P.vert k)).2))
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (heR_span : eR ∈ P.spanningSet y)
    (heR_span_w : eR ∈ P.spanningSet (toReal (P.vert k)).2)
    (hord : P.edgeThr y k < P.edgeThr y eR) :
    (toReal (P.vert k)).1 < P.edgeThr (toReal (P.vert k)).2 eR := by
  classical
  set v := toReal (P.vert k) with hv
  set w := v.2 with hw
  -- descending incident edge `k` spans `y` (upper endpoint `vert k = v`, lower `vert(k+1)`)
  have hkp1_lt_y : (toReal (P.vert (k + 1))).2 < y := by
    rcases lt_trichotomy (toReal (P.vert (k + 1))).2 y with h | h | h
    · exact h
    · exact absurd h (hygen (k + 1))
    · exact absurd ⟨h, hkp1⟩ (hslab (k + 1))
  have hk_span : k ∈ P.spanningSet y := by
    simp only [LatticePolygon.spanningSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨hkp1_lt_y, hyw⟩
  -- edgeThr w k = xv  (bottom of the descending edge)
  have hval2 : P.edgeThr w k = v.1 := by
    rw [LatticePolygon.edgeThr]; exact crossThreshold_bot v (toReal (P.vert (k + 1)))
  obtain ⟨y₀, hy₀y, hslab0⟩ := exists_vertexFree_slab_below P y w hygen hslab
  have hslabM : ∀ i, ¬ (y₀ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w) := hslab0
  have hc_eR : Continuous (fun s => P.edgeThr s eR) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hc_k : Continuous (fun s => P.edgeThr s k) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hyle : v.1 ≤ P.edgeThr w eR := by
    rw [← hval2]
    have hkey : ∀ z ∈ Set.Ioo y w, P.edgeThr z k < P.edgeThr z eR := by
      intro z hz
      have hzM : z ∈ Set.Ioo y₀ w := ⟨lt_trans hy₀y hz.1, hz.2⟩
      have hyM : y ∈ Set.Ioo y₀ w := ⟨hy₀y, hyw⟩
      exact chord_order_preserved_in_slab P hsimple y₀ w hslabM k eR hyM
        hk_span heR_span hord hzM
    have hL : Filter.Tendsto (fun z => P.edgeThr z k) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w k)) := (hc_k.continuousAt).continuousWithinAt
    have hR : Filter.Tendsto (fun z => P.edgeThr z eR) (nhdsWithin w (Set.Iio w))
        (nhds (P.edgeThr w eR)) := (hc_eR.continuousAt).continuousWithinAt
    have hne : (nhdsWithin w (Set.Iio w)).NeBot := nhdsLT_neBot_of_exists_lt ⟨y, hyw⟩
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds hyw)] with z hzlt hzgt
    exact (hkey z ⟨hzgt, hzlt⟩).le
  rcases lt_or_eq_of_le hyle with hlt | heq
  · exact hlt
  · exfalso
    have heR_span_w' : (((toReal (P.vert eR)).2 < w ∧ w < (toReal (P.vert (eR + 1))).2) ∨
        ((toReal (P.vert (eR + 1))).2 < w ∧ w < (toReal (P.vert eR)).2)) := by
      simpa [LatticePolygon.spanningSet, Finset.mem_filter] using heR_span_w
    have hmem : (P.edgeThr w eR, w) ∈ P.edgeSeg eR := by
      rw [LatticePolygon.edgeThr, LatticePolygon.edgeSeg]
      rcases heR_span_w' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact crossThreshold_mem_segment _ _ w h1 h2
      · exact crossThreshold_mem_segment_down _ _ w h1 h2
    rw [← heq] at hmem
    have : v ∈ P.edgeSeg eR := by
      have : (v.1, w) = v := by rw [Prod.ext_iff]; exact ⟨rfl, rfl⟩
      rwa [this] at hmem
    exact vert_notMem_edgeSeg P hsimple k eR heRk heRk1 this

/-- **The apex-crossing routing move (ordered form).** At a strict local-max vertex `k`
with apex `v = (xv, w)`, given the two incident edges `eLft, eRgt` (= `{k-1, k}` in threshold
order) and the two outer flanking chords `eL, eR` (non-incident, spanning the slab and
surviving to `w`), with the threshold chain
`edgeThr y eL < edgeThr y eLft < edgeThr y eRgt < edgeThr y eR` at a generic `y < w` and both
flank gaps `(eL,eLft)`, `(eRgt,eR)` consecutive, any point `(xa,y)` in the left flank gap is
`JoinedIn boundaryᶜ` to any point `(xc,y)` in the right flank gap. The staircase: lift left up
the left gap to a column `xL = xv-ρ` near a height `y₂` just below `w`, go up that column past
`w` to `w+τ`, slide right above the apex to `xR = xv+ρ`, come down the mirror, and lift down the
right gap — all clearances provided by `apex_level_clear`, `exists_clear_above_local_max`,
`apex_thresholds_localize`, and `edgeThr_lt_apex_of_outer`/`apex_lt_edgeThr_of_outer`. -/
lemma apex_cross_ordered (hsimple : P.IsSimple) (k eL eLft eRgt eR : ZMod P.n)
    (hkm1 : (toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2)
    (hkp1 : (toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2)
    (y : ℝ) (hyw : y < (toReal (P.vert k)).2)
    (hslab : ∀ i, ¬ (y < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < (toReal (P.vert k)).2))
    (hygen : ∀ i, (toReal (P.vert i)).2 ≠ y)
    (heLft : eLft = k - 1 ∨ eLft = k) (heRgt : eRgt = k - 1 ∨ eRgt = k) (hLR_inc : eLft ≠ eRgt)
    (heLk : eL ≠ k) (heLk1 : eL ≠ k - 1) (heRk : eR ≠ k) (heRk1 : eR ≠ k - 1)
    (heL_y : eL ∈ P.spanningSet y) (heLft_y : eLft ∈ P.spanningSet y)
    (heRgt_y : eRgt ∈ P.spanningSet y) (heR_y : eR ∈ P.spanningSet y)
    (heL_w : eL ∈ P.spanningSet (toReal (P.vert k)).2)
    (heR_w : eR ∈ P.spanningSet (toReal (P.vert k)).2)
    (ho1 : P.edgeThr y eL < P.edgeThr y eLft)
    (ho2 : P.edgeThr y eLft < P.edgeThr y eRgt)
    (ho3 : P.edgeThr y eRgt < P.edgeThr y eR)
    (hconsL : ∀ i ∈ P.spanningSet y,
      P.edgeThr y i ≤ P.edgeThr y eL ∨ P.edgeThr y eLft ≤ P.edgeThr y i)
    (hconsR : ∀ i ∈ P.spanningSet y,
      P.edgeThr y i ≤ P.edgeThr y eRgt ∨ P.edgeThr y eR ≤ P.edgeThr y i)
    (xa xc : ℝ) (hxa : P.edgeThr y eL < xa ∧ xa < P.edgeThr y eLft)
    (hxc : P.edgeThr y eRgt < xc ∧ xc < P.edgeThr y eR) :
    JoinedIn P.boundaryᶜ (xa, y) (xc, y) := by
  classical
  set v := toReal (P.vert k) with hv
  set w := v.2 with hw
  set xv := v.1 with hxvdef
  -- both incident edges' thresholds dominate eL and are dominated by eR
  have hdkm1 : (toReal (P.vert (k - 1))).2 ≠ w := ne_of_lt hkm1
  have hdk : (toReal (P.vert (k + 1))).2 ≠ w := ne_of_lt hkp1
  -- edgeThr y (k-1) and edgeThr y k are the two incident thresholds; eL is left of both, eR right
  have hkm1_or : P.edgeThr y (k - 1) = P.edgeThr y eLft ∨ P.edgeThr y (k - 1) = P.edgeThr y eRgt := by
    rcases heLft with h | h <;> rcases heRgt with h' | h'
    · exact absurd (h.trans h'.symm) hLR_inc
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h'])
    · exact absurd (h.trans h'.symm) hLR_inc
  have hk_or : P.edgeThr y k = P.edgeThr y eLft ∨ P.edgeThr y k = P.edgeThr y eRgt := by
    rcases heLft with h | h <;> rcases heRgt with h' | h'
    · exact absurd (h.trans h'.symm) hLR_inc
    · exact Or.inr (by rw [h'])
    · exact Or.inl (by rw [h])
    · exact absurd (h.trans h'.symm) hLR_inc
  have heL_lt_km1 : P.edgeThr y eL < P.edgeThr y (k - 1) := by
    rcases hkm1_or with h | h
    · rw [h]; exact ho1
    · rw [h]; exact lt_trans ho1 ho2
  have hk_lt_eR : P.edgeThr y k < P.edgeThr y eR := by
    rcases hk_or with h | h
    · rw [h]; exact lt_trans ho2 ho3
    · rw [h]; exact ho3
  -- Step 1: outer chords are strictly outside the apex abscissa at level w
  have hL₀ : P.edgeThr w eL < xv :=
    edgeThr_lt_apex_of_outer P hsimple k eL hkm1 heLk heLk1 y hyw hslab hygen heL_y heL_w heL_lt_km1
  have hR₀ : xv < P.edgeThr w eR :=
    apex_lt_edgeThr_of_outer P hsimple k eR hkp1 heRk heRk1 y hyw hslab hygen heR_y heR_w hk_lt_eR
  set L₀ := P.edgeThr w eL with hL₀def
  set R₀ := P.edgeThr w eR with hR₀def
  -- clearance constants
  obtain ⟨ε, hε, hclearε⟩ := apex_level_clear P hsimple k hkm1 hkp1
  obtain ⟨δ, hδ, hclearδ⟩ := exists_clear_above_local_max P hsimple k hkm1 hkp1
  -- ρ : positive, < ε, < δ, ≤ (xv-L₀)/2, ≤ (R₀-xv)/2
  set ρ := min (min (ε/2) (δ/2)) (min ((xv - L₀)/2) ((R₀ - xv)/2)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> linarith
  have hρε : ρ < ε := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hρδ : ρ < δ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hρL : ρ ≤ (xv - L₀)/2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρR : ρ ≤ (R₀ - xv)/2 := le_trans (min_le_right _ _) (min_le_right _ _)
  set τ := δ/2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτδ : τ < δ := by rw [hτdef]; linarith
  -- xv - ρ > L₀  and  xv + ρ < R₀
  have hLgap : L₀ < xv - ρ := by have := hρL; linarith
  have hRgap : xv + ρ < R₀ := by have := hρR; linarith
  -- η localizing incident thresholds within ρ of xv
  obtain ⟨η, hη, hηball⟩ := apex_thresholds_localize P k hdkm1 hdk ρ hρpos
  -- continuity of eL, eR thresholds to localize them near L₀, R₀
  have hc_eL : Continuous (fun s => P.edgeThr s eL) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  have hc_eR : Continuous (fun s => P.edgeThr s eR) := by
    simp only [LatticePolygon.edgeThr]; exact continuous_crossThreshold _ _
  -- eventually below w: edgeThr s eL < xv - ρ
  have hevL : ∀ᶠ s in nhds w, P.edgeThr s eL < xv - ρ := by
    have ht : Filter.Tendsto (fun s => P.edgeThr s eL) (nhds w) (nhds L₀) :=
      (hc_eL.continuousAt (x := w)).tendsto
    exact ht.eventually (eventually_lt_nhds hLgap)
  have hevR : ∀ᶠ s in nhds w, xv + ρ < P.edgeThr s eR := by
    have ht : Filter.Tendsto (fun s => P.edgeThr s eR) (nhds w) (nhds R₀) :=
      (hc_eR.continuousAt (x := w)).tendsto
    exact ht.eventually (eventually_gt_nhds hRgap)
  obtain ⟨η', hη', hη'ball⟩ := Metric.eventually_nhds_iff_ball.mp (hevL.and hevR)
  -- choose generic y₂ ∈ (max y (w - min η η'), w)
  set ylo := max y (w - min η η') with hylodef
  have hylo_lt_w : ylo < w := by
    rw [hylodef]; refine max_lt hyw ?_
    have : 0 < min η η' := lt_min hη hη'
    linarith
  obtain ⟨y₂, hy₂lo, hy₂hi, -⟩ := exists_generic_height_mem_Ioo P ylo w hylo_lt_w
  have hy_lt_y₂ : y < y₂ := lt_of_le_of_lt (le_max_left _ _) hy₂lo
  have hy₂_in_slab : y < y₂ ∧ y₂ < w := ⟨hy_lt_y₂, hy₂hi⟩
  -- y₂ is generic (slab (y,w) vertex-free), and within (w-η,w) and (w-η',w)
  have hy₂gen : ∀ i, (toReal (P.vert i)).2 ≠ y₂ := by
    intro i hi; exact hslab i ⟨hi ▸ hy_lt_y₂, hi ▸ hy₂hi⟩
  have hy₂_w_η : w - η < y₂ := by
    have : w - min η η' < y₂ := lt_of_le_of_lt (le_max_right _ _) hy₂lo
    have hmle : min η η' ≤ η := min_le_left _ _; linarith
  have hy₂_w_η' : w - min η η' < y₂ := lt_of_le_of_lt (le_max_right _ _) hy₂lo
  -- incident thresholds within ρ of xv at y₂
  have hinc_y₂ := hηball y₂ (by linarith [hy₂_w_η]) (by linarith [hy₂hi])
  -- eL, eR thresholds localized at y₂
  have hy₂_ball : y₂ ∈ Metric.ball w η' := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor
    · have : min η η' ≤ η' := min_le_right _ _; linarith [hy₂_w_η']
    · linarith [hy₂hi]
  obtain ⟨heL_y₂_lt, heR_y₂_gt⟩ := hη'ball y₂ hy₂_ball
  -- columns
  set xL := xv - ρ with hxLdef
  set xR := xv + ρ with hxRdef
  have hxL_lt_xR : xL < xR := by rw [hxLdef, hxRdef]; linarith
  -- extend the slab below y to make y strictly interior for chord-order preservation
  obtain ⟨y₀, hy₀y, hslab0⟩ := exists_vertexFree_slab_below P y w hygen hslab
  have hslabM : ∀ i, ¬ (y₀ < (toReal (P.vert i)).2 ∧ (toReal (P.vert i)).2 < w) := hslab0
  have hyM : y ∈ Set.Ioo y₀ w := ⟨hy₀y, hyw⟩
  -- spanningSet is constant across the slab (y₀,w)
  have hspanconst : ∀ z ∈ Set.Ioo y₀ w, P.spanningSet z = P.spanningSet y := fun z hz =>
    spanningSet_const_of_slab P y₀ w hslabM hz hyM
  have hgen_slab : ∀ z ∈ Set.Ioo y₀ w, ∀ i, (toReal (P.vert i)).2 ≠ z := by
    intro z hz i hi; exact hslabM i ⟨hi ▸ hz.1, hi ▸ hz.2⟩
  -- distinctness of spanning thresholds at y
  have hdistinct_y : ∀ a b : ZMod P.n, a ∈ P.spanningSet y → b ∈ P.spanningSet y →
      a ≠ b → P.edgeThr y a ≠ P.edgeThr y b := by
    intro a b ha hb hab
    exact crossThreshold_ne_distinct_spanning P hsimple y hygen a b hab
      (by simpa [LatticePolygon.spanningSet, Finset.mem_filter] using ha)
      (by simpa [LatticePolygon.spanningSet, Finset.mem_filter] using hb)
  -- LEFT gap consecutivity preserved across the slab
  have hgapL : ∀ z ∈ Set.Ioo y₀ w, ∀ i ∈ P.spanningSet z,
      P.edgeThr z i ≤ P.edgeThr z eL ∨ P.edgeThr z eLft ≤ P.edgeThr z i := by
    intro z hz i hi
    have hiY : i ∈ P.spanningSet y := by rw [← hspanconst z hz]; exact hi
    rcases hconsL i hiY with hle | hge
    · left
      by_cases hieL : i = eL
      · rw [hieL]
      · have hstrict : P.edgeThr y i < P.edgeThr y eL :=
          lt_of_le_of_ne hle (hdistinct_y i eL hiY heL_y hieL)
        exact le_of_lt (chord_order_preserved_in_slab P hsimple y₀ w hslabM i eL hyM hiY heL_y hstrict hz)
    · right
      by_cases hieLft : i = eLft
      · rw [hieLft]
      · have hstrict : P.edgeThr y eLft < P.edgeThr y i :=
          lt_of_le_of_ne hge (Ne.symm (hdistinct_y i eLft hiY heLft_y hieLft))
        exact le_of_lt (chord_order_preserved_in_slab P hsimple y₀ w hslabM eLft i hyM heLft_y hiY hstrict hz)
  -- RIGHT gap consecutivity preserved across the slab
  have hgapR : ∀ z ∈ Set.Ioo y₀ w, ∀ i ∈ P.spanningSet z,
      P.edgeThr z i ≤ P.edgeThr z eRgt ∨ P.edgeThr z eR ≤ P.edgeThr z i := by
    intro z hz i hi
    have hiY : i ∈ P.spanningSet y := by rw [← hspanconst z hz]; exact hi
    rcases hconsR i hiY with hle | hge
    · left
      by_cases hieRgt : i = eRgt
      · rw [hieRgt]
      · have hstrict : P.edgeThr y i < P.edgeThr y eRgt :=
          lt_of_le_of_ne hle (hdistinct_y i eRgt hiY heRgt_y hieRgt)
        exact le_of_lt (chord_order_preserved_in_slab P hsimple y₀ w hslabM i eRgt hyM hiY heRgt_y hstrict hz)
    · right
      by_cases hieR : i = eR
      · rw [hieR]
      · have hstrict : P.edgeThr y eR < P.edgeThr y i :=
          lt_of_le_of_ne hge (Ne.symm (hdistinct_y i eR hiY heR_y hieR))
        exact le_of_lt (chord_order_preserved_in_slab P hsimple y₀ w hslabM eR i hyM heR_y hiY hstrict hz)
  -- threshold bounds for eL, eLft, eRgt, eR on the sub-slab (y₂, w)
  have hsub_ball : ∀ z, y₂ ≤ z → z < w → z ∈ Set.Ioo y₀ w ∧ z ∈ Metric.ball w η' ∧
      w - η < z ∧ z < w + η := by
    intro z hz1 hz2
    have hz0 : y₀ < z := lt_of_lt_of_le (lt_trans hy₀y hy_lt_y₂) hz1
    have hzη' : z ∈ Metric.ball w η' := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      refine ⟨?_, by linarith⟩
      have h1 : w - η' < y₂ := by
        have : min η η' ≤ η' := min_le_right _ _; linarith [hy₂_w_η']
      linarith
    have hzη : w - η < z := by
      have : w - η < y₂ := by have : min η η' ≤ η := min_le_left _ _; linarith [hy₂_w_η']
      linarith
    exact ⟨⟨hz0, hz2⟩, hzη', hzη, by linarith⟩
  -- LEFT column clear on [y₂, w+τ]
  have hcolL : ∀ z, y₂ ≤ z → z ≤ w + τ → ((xL, z) : ℝ × ℝ) ∉ P.boundary := by
    intro z hz1 hz2
    rcases lt_trichotomy z w with hzw | hzw | hzw
    · -- regime 1: generic z in slab; xL in left gap
      obtain ⟨hzslab, hzη', hzη1, hzη2⟩ := hsub_ball z hz1 hzw
      have hthrL : P.edgeThr z eL < xL := (hη'ball z hzη').1
      have hincz := hηball z hzη1 hzη2
      have hthrLft : xL < P.edgeThr z eLft := by
        rcases heLft with h | h
        · rw [h, hxLdef]; linarith [abs_lt.mp hincz.1]
        · rw [h, hxLdef]; linarith [abs_lt.mp hincz.2]
      exact notMem_boundary_of_between_thresholds P z (hgen_slab z hzslab) xL
        (P.edgeThr z eL) (P.edgeThr z eLft) ⟨hthrL, hthrLft⟩ (hgapL z hzslab)
    · -- regime 2: z = w; apex_level_clear
      subst hzw
      refine hclearε xL ⟨by rw [hxLdef]; linarith, by rw [hxLdef]; linarith⟩ ?_
      rw [hxLdef]; intro h; have := hρpos; linarith
    · -- regime 3: z ∈ (w, w+τ); clear-above box
      refine hclearδ (xL, z) ⟨by rw [hxLdef]; linarith, by rw [hxLdef]; linarith⟩ ⟨hzw, by linarith⟩
  -- RIGHT column clear on [y₂, w+τ]
  have hcolR : ∀ z, y₂ ≤ z → z ≤ w + τ → ((xR, z) : ℝ × ℝ) ∉ P.boundary := by
    intro z hz1 hz2
    rcases lt_trichotomy z w with hzw | hzw | hzw
    · obtain ⟨hzslab, hzη', hzη1, hzη2⟩ := hsub_ball z hz1 hzw
      have hthrR : xR < P.edgeThr z eR := (hη'ball z hzη').2
      have hincz := hηball z hzη1 hzη2
      have hthrRgt : P.edgeThr z eRgt < xR := by
        rcases heRgt with h | h
        · rw [h, hxRdef]; linarith [abs_lt.mp hincz.1]
        · rw [h, hxRdef]; linarith [abs_lt.mp hincz.2]
      exact notMem_boundary_of_between_thresholds P z (hgen_slab z hzslab) xR
        (P.edgeThr z eRgt) (P.edgeThr z eR) ⟨hthrRgt, hthrR⟩ (hgapR z hzslab)
    · subst hzw
      refine hclearε xR ⟨by rw [hxRdef]; linarith, by rw [hxRdef]; linarith⟩ ?_
      rw [hxRdef]; intro h; have := hρpos; linarith
    · refine hclearδ (xR, z) ⟨by rw [hxRdef]; linarith, by rw [hxRdef]; linarith⟩ ⟨hzw, by linarith⟩
  -- TOP horizontal clear at height w+τ between xL and xR (clear-above box)
  have htop : ∀ x, xL ≤ x → x ≤ xR → ((x, w + τ) : ℝ × ℝ) ∉ P.boundary := by
    intro x hx1 hx2
    refine hclearδ (x, w + τ) ⟨by rw [hxLdef] at hx1; linarith, by rw [hxRdef] at hx2; linarith⟩
      ⟨by linarith, by linarith⟩
  -- now assemble the five JoinedIn pieces
  -- piece (a): lift (xa,y) → (xL,y₂) in the left gap (eL,eLft)
  have hpieceA : JoinedIn P.boundaryᶜ ((xa, y) : ℝ × ℝ) (xL, y₂) := by
    refine lift_within_vertexFree_slab P hsimple y y₂ hy_lt_y₂ hygen hy₂gen
      (fun i => ?_) eL eLft heL_y heLft_y ho1 hconsL xa xL hxa ?_
    · exact fun h => hslab i ⟨h.1, lt_trans h.2 hy₂hi⟩
    · refine ⟨heL_y₂_lt, ?_⟩
      rcases heLft with h | h
      · rw [h]; linarith [abs_lt.mp hinc_y₂.1, hxLdef]
      · rw [h]; linarith [abs_lt.mp hinc_y₂.2, hxLdef]
  -- piece (b): vertical (xL,y₂) → (xL,w+τ)
  have hpieceB : JoinedIn P.boundaryᶜ ((xL, y₂) : ℝ × ℝ) (xL, w + τ) := by
    refine joinedIn_vertical_of_endpoints P xL y₂ (w + τ) (by linarith)
      (hcolL y₂ le_rfl (by linarith)) (hcolL (w + τ) (by linarith) le_rfl) ?_
    intro z hz1 hz2; exact hcolL z hz1.le hz2.le
  -- piece (c): horizontal (xL,w+τ) → (xR,w+τ)
  have hpieceC : JoinedIn P.boundaryᶜ ((xL, w + τ) : ℝ × ℝ) (xR, w + τ) := by
    refine joinedIn_horizontal_of_endpoints P (w + τ) xL xR hxL_lt_xR.le
      (htop xL le_rfl hxL_lt_xR.le) (htop xR hxL_lt_xR.le le_rfl) ?_
    intro x hx1 hx2; exact htop x hx1.le hx2.le
  -- piece (d): vertical (xR,w+τ) → (xR,y₂)
  have hpieceD : JoinedIn P.boundaryᶜ ((xR, w + τ) : ℝ × ℝ) (xR, y₂) := by
    refine (joinedIn_vertical_of_endpoints P xR y₂ (w + τ) (by linarith)
      (hcolR y₂ le_rfl (by linarith)) (hcolR (w + τ) (by linarith) le_rfl) ?_).symm
    intro z hz1 hz2; exact hcolR z hz1.le hz2.le
  -- piece (e): lift (xR,y₂) → (xc,y) in the right gap (eRgt,eR) [lift up then symm]
  have hpieceE : JoinedIn P.boundaryᶜ ((xR, y₂) : ℝ × ℝ) (xc, y) := by
    refine (lift_within_vertexFree_slab P hsimple y y₂ hy_lt_y₂ hygen hy₂gen
      (fun i => ?_) eRgt eR heRgt_y heR_y ho3 hconsR xc xR hxc ?_).symm
    · exact fun h => hslab i ⟨h.1, lt_trans h.2 hy₂hi⟩
    · refine ⟨?_, heR_y₂_gt⟩
      rcases heRgt with h | h
      · rw [h]; linarith [abs_lt.mp hinc_y₂.1, hxRdef]
      · rw [h]; linarith [abs_lt.mp hinc_y₂.2, hxRdef]
  exact ((((hpieceA.trans hpieceB).trans hpieceC).trans hpieceD).trans hpieceE)

end InsideConnected

end Pick
