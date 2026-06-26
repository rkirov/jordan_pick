import Top100.PicksTheorem.Defs

/-!
# Basic properties of the integer winding number

Foundational facts about `Pick.LatticePolygon.winding`, the signed ray-crossing
winding number. The key seed result: an edge contributes nothing to the winding
around `q` unless `q.2` lies within the edge's vertical range. Hence the winding
vanishes for points above (or below) every vertex — the start of "the unbounded
component has winding `0`" and of finite support for the lattice sum.
-/

namespace Pick

open LatticePolygon

@[simp] lemma toReal_fst (p : Pt) : (toReal p).1 = (p.1 : ℝ) := rfl
@[simp] lemma toReal_snd (p : Pt) : (toReal p).2 = (p.2 : ℝ) := rfl

/-- How `cross (b−a) (q−a)` shifts under a unit horizontal step of `q`: it
changes by `−(b.2−a.2)`. This governs when `edgeWind` flips as the test point
moves horizontally — the basis of the integer winding's ray-casting. -/
lemma cross_hshift (a b q : ℝ × ℝ) :
    cross (b - a) (q + (1, 0) - a) = cross (b - a) (q - a) - (b.2 - a.2) := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  ring


/-- An edge contributes nothing to the winding around `q` if `q` is (weakly)
above both its endpoints: the upward ray cannot meet it. -/
lemma edgeWind_eq_zero_of_above (a b q : ℝ × ℝ) (ha : a.2 ≤ q.2) (hb : b.2 ≤ q.2) :
    edgeWind a b q = 0 := by
  unfold edgeWind
  have h1 : ¬ (a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)) := by
    rintro ⟨_, h, _⟩; linarith
  have h2 : ¬ (b.2 ≤ q.2 ∧ q.2 < a.2 ∧ cross (b - a) (q - a) < 0) := by
    rintro ⟨_, h, _⟩; linarith
  rw [if_neg h1, if_neg h2]

/-- An edge contributes nothing to the winding around `q` if `q` is strictly
below both its endpoints. -/
lemma edgeWind_eq_zero_of_below (a b q : ℝ × ℝ) (ha : q.2 < a.2) (hb : q.2 < b.2) :
    edgeWind a b q = 0 := by
  unfold edgeWind
  have h1 : ¬ (a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)) := by
    rintro ⟨h, _, _⟩; linarith
  have h2 : ¬ (b.2 ≤ q.2 ∧ q.2 < a.2 ∧ cross (b - a) (q - a) < 0) := by
    rintro ⟨h, _, _⟩; linarith
  rw [if_neg h1, if_neg h2]

/-- An edge not spanning `q`'s height contributes nothing to the horizontal-step
change of the winding (it is `0` at both `q` and `q + (1,0)`, which share their
`y`-coordinate). So only `y`-spanning edges matter for the ray-casting. -/
lemma edgeWind_hshift_eq_zero_of_out (a b q : ℝ × ℝ)
    (h : (q.2 < a.2 ∧ q.2 < b.2) ∨ (a.2 ≤ q.2 ∧ b.2 ≤ q.2)) :
    edgeWind a b (q + (1, 0)) - edgeWind a b q = 0 := by
  have hq2 : (q + (1, 0)).2 = q.2 := by simp [Prod.snd_add]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [edgeWind_eq_zero_of_below a b q h1 h2,
      edgeWind_eq_zero_of_below a b (q + (1, 0)) (by rw [hq2]; exact h1) (by rw [hq2]; exact h2)]
    ring
  · rw [edgeWind_eq_zero_of_above a b q h1 h2,
      edgeWind_eq_zero_of_above a b (q + (1, 0)) (by rw [hq2]; exact h1) (by rw [hq2]; exact h2)]
    ring

/-- The discrete derivative of the winding number under a unit horizontal step:
the sum over edges of the per-edge `edgeWind` change. (Only `y`-spanning edges
contribute, by `edgeWind_hshift_eq_zero_of_out`.) -/
lemma winding_hshift (P : LatticePolygon) (q : ℝ × ℝ) :
    P.winding (q + (1, 0)) - P.winding q
      = ∑ i, (edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (q + (1, 0))
              - edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q) := by
  unfold LatticePolygon.winding
  rw [← Finset.sum_sub_distrib]

/-- Local constancy fragment: the winding is unchanged by a horizontal step when
no edge spans `q`'s height (every edge contributes `0` to the step). -/
lemma winding_hshift_eq_of_no_span (P : LatticePolygon) (q : ℝ × ℝ)
    (h : ∀ i, (q.2 < (toReal (P.vert i)).2 ∧ q.2 < (toReal (P.vert (i + 1))).2)
         ∨ ((toReal (P.vert i)).2 ≤ q.2 ∧ (toReal (P.vert (i + 1))).2 ≤ q.2)) :
    P.winding (q + (1, 0)) = P.winding q := by
  have hz := winding_hshift P q
  rw [Finset.sum_eq_zero fun i _ => edgeWind_hshift_eq_zero_of_out _ _ q (h i)] at hz
  exact sub_eq_zero.mp hz

/-- An edge contributes nothing to the winding around `q` if `q` is strictly to
the right of both endpoints: the rightward ray starts past the whole edge.
The certificate is `cross (b-a) (q-a) = -[(b.2-q.2)(q.1-a.1) + (q.2-a.2)(q.1-b.1)]`,
each bracketed product having a forced sign on each branch. -/
lemma edgeWind_eq_zero_of_right (a b q : ℝ × ℝ) (ha : a.1 < q.1) (hb : b.1 < q.1) :
    edgeWind a b q = 0 := by
  unfold edgeWind cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  have h1 : ¬ (a.2 ≤ q.2 ∧ q.2 < b.2 ∧
      0 < (b.1 - a.1) * (q.2 - a.2) - (b.2 - a.2) * (q.1 - a.1)) := by
    rintro ⟨ha2, hb2, h3⟩
    nlinarith [mul_pos (show (0:ℝ) < b.2 - q.2 by linarith) (show (0:ℝ) < q.1 - a.1 by linarith),
      mul_nonneg (show (0:ℝ) ≤ q.2 - a.2 by linarith) (show (0:ℝ) ≤ q.1 - b.1 by linarith)]
  have h2 : ¬ (b.2 ≤ q.2 ∧ q.2 < a.2 ∧
      (b.1 - a.1) * (q.2 - a.2) - (b.2 - a.2) * (q.1 - a.1) < 0) := by
    rintro ⟨ha2, hb2, h3⟩
    nlinarith [mul_nonneg (show (0:ℝ) ≤ q.2 - b.2 by linarith) (show (0:ℝ) ≤ q.1 - a.1 by linarith),
      mul_pos (show (0:ℝ) < a.2 - q.2 by linarith) (show (0:ℝ) < q.1 - b.1 by linarith)]
  rw [if_neg h1, if_neg h2]

/-- An edge entirely to the left of `q` contributes nothing to the horizontal
step (it stays right of both `q` and `q+(1,0)`). With `edgeWind_hshift_eq_zero_of_out`
this localizes the winding change to edges the step actually crosses. -/
lemma edgeWind_hshift_eq_zero_of_right (a b q : ℝ × ℝ) (ha : a.1 < q.1) (hb : b.1 < q.1) :
    edgeWind a b (q + (1, 0)) - edgeWind a b q = 0 := by
  have hq1 : q.1 < (q + (1, 0)).1 := by simp [Prod.fst_add]
  rw [edgeWind_eq_zero_of_right a b q ha hb,
    edgeWind_eq_zero_of_right a b (q + (1, 0)) (by linarith) (by linarith)]
  ring

/-- The winding number vanishes for points strictly to the right of every
vertex. -/
lemma winding_eq_zero_of_right (P : LatticePolygon) (q : ℝ × ℝ)
    (h : ∀ i, ((P.vert i).1 : ℝ) < q.1) : P.winding q = 0 := by
  unfold LatticePolygon.winding
  refine Finset.sum_eq_zero fun i _ => ?_
  exact edgeWind_eq_zero_of_right _ _ _ (by simpa using h i) (by simpa using h (i + 1))

/-- For `q` strictly left of both endpoints, the edge's contribution is the
"step difference" `[q.2 < b.2] − [q.2 < a.2]`. (The rightward ray always meets
such an edge when their `y`-ranges overlap, so this does *not* vanish per-edge;
it telescopes over the closed polygon instead.) -/
lemma edgeWind_far_left (a b q : ℝ × ℝ) (ha : q.1 < a.1) (hb : q.1 < b.1) :
    edgeWind a b q = (if q.2 < b.2 then (1:ℤ) else 0) - (if q.2 < a.2 then 1 else 0) := by
  unfold edgeWind cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  set X := (b.1 - a.1) * (q.2 - a.2) - (b.2 - a.2) * (q.1 - a.1) with hX
  have up : a.2 ≤ q.2 → q.2 < b.2 → 0 < X := by
    intro h1 h2
    nlinarith [mul_pos (show (0:ℝ) < b.2 - q.2 by linarith) (show (0:ℝ) < a.1 - q.1 by linarith),
      mul_nonneg (show (0:ℝ) ≤ q.2 - a.2 by linarith) (show (0:ℝ) ≤ b.1 - q.1 by linarith)]
  have dn : b.2 ≤ q.2 → q.2 < a.2 → X < 0 := by
    intro h1 h2
    nlinarith [mul_pos (show (0:ℝ) < a.2 - q.2 by linarith) (show (0:ℝ) < b.1 - q.1 by linarith),
      mul_nonneg (show (0:ℝ) ≤ q.2 - b.2 by linarith) (show (0:ℝ) ≤ a.1 - q.1 by linarith)]
  by_cases h1 : q.2 < a.2 <;> by_cases h2 : q.2 < b.2
  · rw [if_neg (by rintro ⟨h, _, _⟩; linarith), if_neg (by rintro ⟨h, _, _⟩; linarith)]
    simp [h1, h2]
  · rw [if_neg (by rintro ⟨h, _, _⟩; linarith),
        if_pos ⟨not_lt.mp h2, h1, dn (not_lt.mp h2) h1⟩]
    simp [h1, h2]
  · rw [if_pos ⟨not_lt.mp h1, h2, up (not_lt.mp h1) h2⟩]
    simp [h1, h2]
  · rw [if_neg (by rintro ⟨_, h, _⟩; linarith), if_neg (by rintro ⟨_, h, _⟩; linarith)]
    simp [h1, h2]

/-- The winding number vanishes for points strictly to the left of every vertex:
the step contributions telescope over the closed (cyclic) polygon. -/
lemma winding_eq_zero_of_left (P : LatticePolygon) (q : ℝ × ℝ)
    (h : ∀ i, q.1 < ((P.vert i).1 : ℝ)) : P.winding q = 0 := by
  classical
  set g : ZMod P.n → ℤ := fun i => if q.2 < (toReal (P.vert i)).2 then (1 : ℤ) else 0 with hg
  have key : ∀ i, edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q = g (i + 1) - g i := by
    intro i
    exact edgeWind_far_left (toReal (P.vert i)) (toReal (P.vert (i + 1))) q
      (by simpa using h i) (by simpa using h (i + 1))
  unfold LatticePolygon.winding
  have reindex : (∑ i, g (i + 1)) = ∑ i, g i :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n)) g
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, reindex, sub_self]

/-- `edgeWind` only takes the values `-1`, `0`, `1`. -/
lemma edgeWind_mem (a b q : ℝ × ℝ) : edgeWind a b q = -1 ∨ edgeWind a b q = 0 ∨ edgeWind a b q = 1 := by
  unfold edgeWind
  split_ifs <;> simp

/-- If an edge's contribution is `+1`, the test point is in the (upward) `y`-range
`[a.2, b.2)`. -/
lemma edgeWind_eq_one_imp (a b q : ℝ × ℝ) (h : edgeWind a b q = 1) :
    a.2 ≤ q.2 ∧ q.2 < b.2 := by
  unfold edgeWind at h
  by_cases h1 : a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)
  · exact ⟨h1.1, h1.2.1⟩
  · rw [if_neg h1] at h
    by_cases h2 : b.2 ≤ q.2 ∧ q.2 < a.2 ∧ cross (b - a) (q - a) < 0
    · rw [if_pos h2] at h; exact absurd h (by decide)
    · rw [if_neg h2] at h; exact absurd h (by decide)

/-- If an edge's contribution is `−1`, the test point is in the (downward)
`y`-range `[b.2, a.2)`. -/
lemma edgeWind_eq_neg_one_imp (a b q : ℝ × ℝ) (h : edgeWind a b q = -1) :
    b.2 ≤ q.2 ∧ q.2 < a.2 := by
  unfold edgeWind at h
  by_cases h1 : a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)
  · rw [if_pos h1] at h; exact absurd h (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : b.2 ≤ q.2 ∧ q.2 < a.2 ∧ cross (b - a) (q - a) < 0
    · exact ⟨h2.1, h2.2.1⟩
    · rw [if_neg h2] at h; exact absurd h (by decide)

/-- A point left of an upward edge (within its `y`-range) lies strictly left of
the edge line, so `cross > 0`. Reusable "side of the edge" criterion for the
crossing argument. -/
lemma cross_pos_of_left (a b q : ℝ × ℝ) (h1 : a.2 ≤ q.2) (h2 : q.2 < b.2)
    (ha : q.1 < a.1) (hb : q.1 < b.1) : 0 < cross (b - a) (q - a) := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  nlinarith [mul_pos (show (0:ℝ) < b.2 - q.2 by linarith) (show (0:ℝ) < a.1 - q.1 by linarith),
    mul_nonneg (show (0:ℝ) ≤ q.2 - a.2 by linarith) (show (0:ℝ) ≤ b.1 - q.1 by linarith)]

/-- A point left of a downward edge (within its `y`-range) lies strictly left of
the edge line, so `cross < 0`. -/
lemma cross_neg_of_left (a b q : ℝ × ℝ) (h1 : b.2 ≤ q.2) (h2 : q.2 < a.2)
    (ha : q.1 < a.1) (hb : q.1 < b.1) : cross (b - a) (q - a) < 0 := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ q.2 - b.2 by linarith) (show (0:ℝ) ≤ a.1 - q.1 by linarith),
    mul_pos (show (0:ℝ) < a.2 - q.2 by linarith) (show (0:ℝ) < b.1 - q.1 by linarith)]

/-- A point right of an upward edge (within its `y`-range) has `cross < 0`. -/
lemma cross_neg_of_right (a b q : ℝ × ℝ) (h1 : a.2 ≤ q.2) (h2 : q.2 < b.2)
    (ha : a.1 < q.1) (hb : b.1 < q.1) : cross (b - a) (q - a) < 0 := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  nlinarith [mul_pos (show (0:ℝ) < b.2 - q.2 by linarith) (show (0:ℝ) < q.1 - a.1 by linarith),
    mul_nonneg (show (0:ℝ) ≤ q.2 - a.2 by linarith) (show (0:ℝ) ≤ q.1 - b.1 by linarith)]

/-- A point right of a downward edge (within its `y`-range) has `cross > 0`. -/
lemma cross_pos_of_right (a b q : ℝ × ℝ) (h1 : b.2 ≤ q.2) (h2 : q.2 < a.2)
    (ha : a.1 < q.1) (hb : b.1 < q.1) : 0 < cross (b - a) (q - a) := by
  unfold cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ q.2 - b.2 by linarith) (show (0:ℝ) ≤ q.1 - a.1 by linarith),
    mul_pos (show (0:ℝ) < a.2 - q.2 by linarith) (show (0:ℝ) < q.1 - b.1 by linarith)]

/-- `edgeWind = 1` exactly characterizes the upward-crossing condition. -/
lemma edgeWind_eq_one_iff (a b q : ℝ × ℝ) :
    edgeWind a b q = 1 ↔ a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a) := by
  constructor
  · intro h
    unfold edgeWind at h
    by_cases h1 : a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)
    · exact h1
    · rw [if_neg h1] at h; split_ifs at h <;> simp_all
  · intro h; unfold edgeWind; rw [if_pos h]

/-- `edgeWind = −1` exactly characterizes the downward-crossing condition. -/
lemma edgeWind_eq_neg_one_iff (a b q : ℝ × ℝ) :
    edgeWind a b q = -1 ↔ b.2 ≤ q.2 ∧ q.2 < a.2 ∧ cross (b - a) (q - a) < 0 := by
  constructor
  · intro h
    unfold edgeWind at h
    by_cases h1 : a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : b.2 ≤ q.2 ∧ q.2 < a.2 ∧ cross (b - a) (q - a) < 0
      · exact h2
      · rw [if_neg h2] at h; exact absurd h (by decide)
  · intro h
    unfold edgeWind
    have h1 : ¬ (a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)) := by
      rintro ⟨_, _, hc⟩; linarith [h.2.2]
    rw [if_neg h1, if_pos h]

/-- An edge entirely to the right of the step contributes nothing: `q` and
`q+(1,0)` are both left of the edge, so the edge gives the same value at each.
With `_of_out` and `_of_right` this localizes the winding change to edges whose
height-`q.2` crossing lies in `(q.1, q.1+1]`. -/
lemma edgeWind_hshift_eq_zero_of_left (a b q : ℝ × ℝ) (ha : q.1 + 1 < a.1) (hb : q.1 + 1 < b.1) :
    edgeWind a b (q + (1, 0)) - edgeWind a b q = 0 := by
  have hq2 : (q + (1, 0)).2 = q.2 := by simp [Prod.snd_add]
  have hq1 : (q + (1, 0)).1 = q.1 + 1 := by simp [Prod.fst_add]
  suffices h : edgeWind a b q = edgeWind a b (q + (1, 0)) by rw [h]; ring
  by_cases hup : a.2 ≤ q.2 ∧ q.2 < b.2
  · rw [(edgeWind_eq_one_iff a b q).mpr
        ⟨hup.1, hup.2, cross_pos_of_left a b q hup.1 hup.2 (by linarith) (by linarith)⟩,
      (edgeWind_eq_one_iff a b (q + (1, 0))).mpr
        ⟨by rw [hq2]; exact hup.1, by rw [hq2]; exact hup.2,
         cross_pos_of_left a b (q + (1, 0)) (by rw [hq2]; exact hup.1) (by rw [hq2]; exact hup.2)
           (by rw [hq1]; linarith) (by rw [hq1]; linarith)⟩]
  · by_cases hdn : b.2 ≤ q.2 ∧ q.2 < a.2
    · rw [(edgeWind_eq_neg_one_iff a b q).mpr
          ⟨hdn.1, hdn.2, cross_neg_of_left a b q hdn.1 hdn.2 (by linarith) (by linarith)⟩,
        (edgeWind_eq_neg_one_iff a b (q + (1, 0))).mpr
          ⟨by rw [hq2]; exact hdn.1, by rw [hq2]; exact hdn.2,
           cross_neg_of_left a b (q + (1, 0)) (by rw [hq2]; exact hdn.1) (by rw [hq2]; exact hdn.2)
             (by rw [hq1]; linarith) (by rw [hq1]; linarith)⟩]
    · have h0q : edgeWind a b q = 0 := by
        rcases edgeWind_mem a b q with h | h | h
        · exact absurd (edgeWind_eq_neg_one_imp a b q h) hdn
        · exact h
        · exact absurd (edgeWind_eq_one_imp a b q h) hup
      have h0q' : edgeWind a b (q + (1, 0)) = 0 := by
        rcases edgeWind_mem a b (q + (1, 0)) with h | h | h
        · have h' := edgeWind_eq_neg_one_imp a b (q + (1, 0)) h; rw [hq2] at h'; exact absurd h' hdn
        · exact h
        · have h' := edgeWind_eq_one_imp a b (q + (1, 0)) h; rw [hq2] at h'; exact absurd h' hup
      rw [h0q, h0q']

/-- **Local constancy.** The winding is unchanged by a horizontal step when no
edge crosses the step segment: each edge is either out of `q`'s height-range, or
entirely left of `q`, or entirely right of `q+(1,0)`. -/
lemma winding_hshift_eq (P : LatticePolygon) (q : ℝ × ℝ)
    (h : ∀ i,
      ((q.2 < (toReal (P.vert i)).2 ∧ q.2 < (toReal (P.vert (i + 1))).2) ∨
        ((toReal (P.vert i)).2 ≤ q.2 ∧ (toReal (P.vert (i + 1))).2 ≤ q.2)) ∨
      ((toReal (P.vert i)).1 < q.1 ∧ (toReal (P.vert (i + 1))).1 < q.1) ∨
      (q.1 + 1 < (toReal (P.vert i)).1 ∧ q.1 + 1 < (toReal (P.vert (i + 1))).1)) :
    P.winding (q + (1, 0)) = P.winding q := by
  have hzero : ∀ i ∈ Finset.univ,
      edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (q + (1, 0))
        - edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q = 0 := by
    intro i _
    rcases h i with hy | hl | hr
    · exact edgeWind_hshift_eq_zero_of_out _ _ q hy
    · exact edgeWind_hshift_eq_zero_of_right _ _ q hl.1 hl.2
    · exact edgeWind_hshift_eq_zero_of_left _ _ q hr.1 hr.2
  have hz := winding_hshift P q
  rw [Finset.sum_eq_zero hzero] at hz
  exact sub_eq_zero.mp hz

/-- The jump value when a horizontal step crosses an **up-edge** (`q` left of it,
`q+(1,0)` on/right of it): the edge's contribution drops from `1` to `0`, so the
per-edge change is `−1`. -/
lemma edgeWind_hshift_cross_up (a b q : ℝ × ℝ) (h1 : a.2 ≤ q.2) (h2 : q.2 < b.2)
    (hl : 0 < cross (b - a) (q - a)) (hr : cross (b - a) (q + (1, 0) - a) ≤ 0) :
    edgeWind a b (q + (1, 0)) - edgeWind a b q = -1 := by
  have hq2 : (q + (1, 0)).2 = q.2 := by simp [Prod.snd_add]
  rw [(edgeWind_eq_one_iff a b q).mpr ⟨h1, h2, hl⟩]
  have h0 : edgeWind a b (q + (1, 0)) = 0 := by
    rcases edgeWind_mem a b (q + (1, 0)) with h | h | h
    · have h' := edgeWind_eq_neg_one_imp a b (q + (1, 0)) h
      rw [hq2] at h'; linarith [h'.2]
    · exact h
    · have h' := (edgeWind_eq_one_iff a b (q + (1, 0))).mp h
      linarith [h'.2.2]
  rw [h0]; ring

/-- The jump value when a horizontal step crosses a **down-edge** (`q` left of it,
`q+(1,0)` on/right of it): the contribution rises from `−1` to `0`, so the
per-edge change is `+1`. -/
lemma edgeWind_hshift_cross_down (a b q : ℝ × ℝ) (h1 : b.2 ≤ q.2) (h2 : q.2 < a.2)
    (hl : cross (b - a) (q - a) < 0) (hr : 0 ≤ cross (b - a) (q + (1, 0) - a)) :
    edgeWind a b (q + (1, 0)) - edgeWind a b q = 1 := by
  have hq2 : (q + (1, 0)).2 = q.2 := by simp [Prod.snd_add]
  rw [(edgeWind_eq_neg_one_iff a b q).mpr ⟨h1, h2, hl⟩]
  have h0 : edgeWind a b (q + (1, 0)) = 0 := by
    rcases edgeWind_mem a b (q + (1, 0)) with h | h | h
    · have h' := (edgeWind_eq_neg_one_iff a b (q + (1, 0))).mp h; linarith [h'.2.2]
    · exact h
    · have h' := edgeWind_eq_one_imp a b (q + (1, 0)) h; rw [hq2] at h'; linarith [h'.2]
  rw [h0]; ring

/-- The winding's per-edge change under a horizontal step is at most `1` in
absolute value: an edge cannot flip `+1 ↔ −1` in one step, since those require
incompatible `y`-ranges (and `q.2` is unchanged). -/
lemma edgeWind_hshift_abs_le (a b q : ℝ × ℝ) :
    |edgeWind a b (q + (1, 0)) - edgeWind a b q| ≤ 1 := by
  have h2 : (q + (1, 0)).2 = q.2 := by simp [Prod.snd_add]
  rcases edgeWind_mem a b q with hq | hq | hq <;>
    rcases edgeWind_mem a b (q + (1, 0)) with hq' | hq' | hq' <;> rw [hq, hq'] <;>
    first
    | decide
    | (exfalso
       have h3 := edgeWind_eq_one_imp a b q hq
       have h4 := edgeWind_eq_neg_one_imp a b (q + (1, 0)) hq'
       rw [h2] at h4; linarith [h3.1, h3.2, h4.1, h4.2])
    | (exfalso
       have h3 := edgeWind_eq_neg_one_imp a b q hq
       have h4 := edgeWind_eq_one_imp a b (q + (1, 0)) hq'
       rw [h2] at h4; linarith [h3.1, h3.2, h4.1, h4.2])

/-- `cross` depends only on the differences, so it is invariant under a common
translation of all three points. -/
lemma cross_shift (a b q c : ℝ × ℝ) :
    cross (b + c - (a + c)) (q + c - (a + c)) = cross (b - a) (q - a) := by
  have h1 : b + c - (a + c) = b - a := by abel
  have h2 : q + c - (a + c) = q - a := by abel
  rw [h1, h2]

/-- The per-edge winding contribution is translation invariant. -/
lemma edgeWind_add_right (a b q c : ℝ × ℝ) :
    edgeWind (a + c) (b + c) (q + c) = edgeWind a b q := by
  unfold edgeWind
  simp only [Prod.snd_add, add_le_add_iff_right, add_lt_add_iff_right, cross_shift]

/-- The winding number vanishes for points weakly above every vertex. -/
lemma winding_eq_zero_of_above (P : LatticePolygon) (q : ℝ × ℝ)
    (h : ∀ i, ((P.vert i).2 : ℝ) ≤ q.2) : P.winding q = 0 := by
  unfold LatticePolygon.winding
  refine Finset.sum_eq_zero fun i _ => ?_
  exact edgeWind_eq_zero_of_above _ _ _ (by simpa using h i) (by simpa using h (i + 1))

/-- The winding number vanishes for points strictly below every vertex. -/
lemma winding_eq_zero_of_below (P : LatticePolygon) (q : ℝ × ℝ)
    (h : ∀ i, q.2 < ((P.vert i).2 : ℝ)) : P.winding q = 0 := by
  unfold LatticePolygon.winding
  refine Finset.sum_eq_zero fun i _ => ?_
  exact edgeWind_eq_zero_of_below _ _ _ (by simpa using h i) (by simpa using h (i + 1))

/-- **Finite support of the winding number.** Only lattice points inside the
vertex bounding box can have nonzero winding, so the support is finite and the
lattice sum `∑_{q ∈ ℤ²} winding P q` is well-defined. -/
theorem winding_support_finite (P : LatticePolygon) :
    {q : Pt | P.winding (toReal q) ≠ 0}.Finite := by
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
    Finset.le_max' (Finset.univ.image (fun j => (P.vert j).1)) ((P.vert i).1)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hym : ∀ i, ym ≤ (P.vert i).2 := fun i =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hyM : ∀ i, (P.vert i).2 ≤ yM := fun i =>
    Finset.le_max' (Finset.univ.image (fun j => (P.vert j).2)) ((P.vert i).2)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine Set.Finite.subset (Set.finite_Icc ((xm, ym) : Pt) (xM, yM)) ?_
  intro q hq
  have hr : ∃ i, q.1 ≤ (P.vert i).1 := by
    by_contra hc; push_neg at hc
    exact hq (winding_eq_zero_of_right P (toReal q) (fun i => by simpa using hc i))
  have hl : ∃ i, (P.vert i).1 ≤ q.1 := by
    by_contra hc; push_neg at hc
    exact hq (winding_eq_zero_of_left P (toReal q) (fun i => by simpa using hc i))
  have ha : ∃ i, q.2 < (P.vert i).2 := by
    by_contra hc; push_neg at hc
    exact hq (winding_eq_zero_of_above P (toReal q) (fun i => by simpa using hc i))
  have hb : ∃ i, (P.vert i).2 ≤ q.2 := by
    by_contra hc; push_neg at hc
    exact hq (winding_eq_zero_of_below P (toReal q) (fun i => by simpa using hc i))
  obtain ⟨ir, hir⟩ := hr; obtain ⟨il, hil⟩ := hl
  obtain ⟨ia, hia⟩ := ha; obtain ⟨ib, hib⟩ := hb
  simp only [Set.mem_Icc, Prod.le_def]
  exact ⟨⟨(hxm il).trans hil, (hym ib).trans hib⟩,
    hir.trans (hxM ir), (le_of_lt hia).trans (hyM ia)⟩

/-- The interior lattice points form a finite set: they sit inside the (finite)
support of the winding number. So `I` is well-defined. -/
theorem interiorLattice_finite (P : LatticePolygon) : P.interiorLattice.Finite := by
  refine Set.Finite.subset (winding_support_finite P) ?_
  intro q hq
  have : P.winding (toReal q) = 1 := hq.1
  simp only [Set.mem_setOf_eq, this, ne_eq, one_ne_zero, not_false_eq_true]

/-- The boundary lattice points form a finite set: the boundary lies in the
convex bounding box of the vertices. So `B` is well-defined. -/
theorem boundaryLattice_finite (P : LatticePolygon) : P.boundaryLattice.Finite := by
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
  have hconv : Convex ℝ (Set.Icc (((xm : ℝ), (ym : ℝ)) : ℝ × ℝ) ((xM : ℝ), (yM : ℝ))) :=
    convex_Icc _ _
  have hvert : ∀ i, toReal (P.vert i) ∈
      Set.Icc (((xm : ℝ), (ym : ℝ)) : ℝ × ℝ) ((xM : ℝ), (yM : ℝ)) := by
    intro i
    simp only [Set.mem_Icc, Prod.le_def, toReal]
    exact ⟨⟨by exact_mod_cast hxm i, by exact_mod_cast hym i⟩,
      by exact_mod_cast hxM i, by exact_mod_cast hyM i⟩
  refine Set.Finite.subset (Set.finite_Icc ((xm, ym) : Pt) (xM, yM)) ?_
  intro q hq
  rw [LatticePolygon.boundaryLattice, Set.mem_setOf_eq, LatticePolygon.boundary,
    Set.mem_iUnion] at hq
  obtain ⟨i, hqi⟩ := hq
  rw [LatticePolygon.edgeSeg] at hqi
  have hmem : toReal q ∈ Set.Icc (((xm : ℝ), (ym : ℝ)) : ℝ × ℝ) ((xM : ℝ), (yM : ℝ)) :=
    hconv.segment_subset (hvert i) (hvert (i + 1)) hqi
  simp only [Set.mem_Icc, Prod.le_def, toReal] at hmem
  simp only [Set.mem_Icc, Prod.le_def]
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hmem
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- The winding number is a measurable function (a finite sum of piecewise-constant
functions on measurable half-spaces). -/
lemma measurable_winding (P : LatticePolygon) : Measurable P.winding := by
  unfold LatticePolygon.winding
  refine Finset.measurable_sum _ fun i _ => ?_
  unfold edgeWind cross
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · measurability
  · measurability

/-- The interior region is measurable, so its Lebesgue measure (`area`) is
well-defined. -/
theorem interiorRegion_measurableSet (P : LatticePolygon) :
    MeasurableSet P.interiorRegion :=
  measurable_winding P (measurableSet_singleton 1)

/-- The interior region is bounded: it lies in the real bounding box of the
vertices (via the four real winding-vanishing lemmas). So `area` is finite. -/
theorem interiorRegion_bounded (P : LatticePolygon) :
    Bornology.IsBounded P.interiorRegion := by
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
  intro q hq
  have hq1 : P.winding q = 1 := hq
  have hw : P.winding q ≠ 0 := by rw [hq1]; exact one_ne_zero
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

/-- The interior region has finite volume (it is bounded), so `area` is a genuine
finite real, not `∞`. -/
theorem interiorRegion_volume_ne_top (P : LatticePolygon) :
    MeasureTheory.volume P.interiorRegion ≠ ⊤ :=
  (interiorRegion_bounded P).measure_lt_top.ne

/-- Interior and boundary lattice points are disjoint (one is off the boundary,
the other on it). So `I + B` counts each enclosed-or-boundary point once. -/
theorem interiorLattice_disjoint_boundaryLattice (P : LatticePolygon) :
    Disjoint P.interiorLattice P.boundaryLattice := by
  rw [Set.disjoint_left]
  exact fun q hq hq' => hq.2 hq'

/-- Every vertex is a boundary lattice point (it is an endpoint of its edge). -/
theorem vert_mem_boundaryLattice (P : LatticePolygon) (i : ZMod P.n) :
    P.vert i ∈ P.boundaryLattice := by
  rw [LatticePolygon.boundaryLattice, Set.mem_setOf_eq, LatticePolygon.boundary, Set.mem_iUnion]
  exact ⟨i, by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩

/-- The boundary always contains at least the vertices, so `1 ≤ B`. -/
theorem one_le_B (P : LatticePolygon) : 1 ≤ P.B := by
  have hne : P.boundaryLattice.Nonempty := ⟨P.vert 0, vert_mem_boundaryLattice P 0⟩
  have h := (Set.ncard_pos (boundaryLattice_finite P)).mpr hne
  show 1 ≤ P.boundaryLattice.ncard
  omega

end Pick
