import JordanPick.PicksTheorem.Weight
import JordanPick.PicksTheorem.Area

/-!
# The per-edge identity (bridging the count side and the area side)

Combines the `ℚ`-valued lattice-point weight `latWeightSum` (Weight.lean) with the
`ℝ`-valued `trapezoidArea` (Area.lean): for a lattice edge with endpoints in the
box, the (cast) weight sum equals the trapezoid area.
-/

namespace Pick

/-- **Per-edge identity in `ℝ`** (all cases): for an edge with endpoints in the
box, the cast weight sum equals the trapezoid area. -/
lemma latWeightSum_eq_trapezoid_real (u v : Pt) (r : ℕ) (hu : u ∈ Box r) (hv : v ∈ Box r) :
    ((latWeightSum u v r : ℚ) : ℝ) = trapezoidArea (toReal u) (toReal v) := by
  rw [latWeightSum_eq_trapezoid u v r hu hv, ← count_value_eq_trapezoid u v]
  push_cast
  ring

open LatticePolygon in
/-- **Step 1 complete (shoelace side).** For a box containing all vertices, the
shoelace area equals the sum over edges of the lattice-point weight `latWeightSum`.
Expanding `latWeightSum`, this is `shoelace = ∑_{q ∈ Box r} ∑ᵢ latWeight (vᵢ−q) (vᵢ₊₁−q)`,
i.e. `shoelace = ∑_q ŵ(q)`. -/
theorem shoelace_eq_sum_latWeightSum (P : LatticePolygon) (r : ℕ) (hr : ∀ i, P.vert i ∈ Box r) :
    P.shoelace = ∑ i, ((latWeightSum (P.vert i) (P.vert (i + 1)) r : ℚ) : ℝ) := by
  rw [← sum_trapezoidArea_eq_shoelace P]
  exact Finset.sum_congr rfl fun i _ =>
    (latWeightSum_eq_trapezoid_real (P.vert i) (P.vert (i + 1)) r (hr i) (hr (i + 1))).symm

/-- **Step 1, final form.** The shoelace area equals the sum over lattice points
`q` in the box of the angle-weight `ŵ(q) = ∑ᵢ latWeight (vᵢ−q) (vᵢ₊₁−q)`. This is
the count-side quantity Step 3 connects to `I + B/2 − 1`. -/
theorem shoelace_eq_totalWeight (P : LatticePolygon) (r : ℕ) (hr : ∀ i, P.vert i ∈ Box r) :
    P.shoelace =
      ((∑ q ∈ Box r, ∑ i, latWeight (P.vert i - q) (P.vert (i + 1) - q) : ℚ) : ℝ) := by
  rw [shoelace_eq_sum_latWeightSum P r hr, ← Rat.cast_sum]
  congr 1
  simp only [latWeightSum]
  rw [Finset.sum_comm]

/-- The polygon's angle-weight at a lattice point `q`: `ŵ(q) = ∑ᵢ latWeight
(vᵢ−q) (vᵢ₊₁−q)`. For `q` off the polygon this is the winding number; on the
boundary it is the fractional interior-angle count. (Step 3 connects `∑_q ŵ(q)`
to `I + B/2 − 1`.) -/
def angleWeight (P : LatticePolygon) (q : Pt) : ℚ :=
  ∑ i, latWeight (P.vert i - q) (P.vert (i + 1) - q)

/-- The angle-weight vanishes for points to the right of every vertex (every edge
contributes `0`, both endpoints having negative `x`-coordinate). -/
lemma angleWeight_eq_zero_of_far_right (P : LatticePolygon) (q : Pt)
    (h : ∀ i, (P.vert i).1 < q.1) : angleWeight P q = 0 := by
  refine Finset.sum_eq_zero fun i _ => latWeight_eq_zero_of_sign_eq _ _ ?_
  simp only [Prod.fst_sub]
  rw [Int.sign_eq_neg_one_of_neg (by have := h i; omega),
    Int.sign_eq_neg_one_of_neg (by have := h (i + 1); omega)]

/-- The angle-weight vanishes for points to the left of every vertex. -/
lemma angleWeight_eq_zero_of_far_left (P : LatticePolygon) (q : Pt)
    (h : ∀ i, q.1 < (P.vert i).1) : angleWeight P q = 0 := by
  refine Finset.sum_eq_zero fun i _ => latWeight_eq_zero_of_sign_eq _ _ ?_
  simp only [Prod.fst_sub]
  rw [Int.sign_eq_one_of_pos (by have := h i; omega),
    Int.sign_eq_one_of_pos (by have := h (i + 1); omega)]

/-- The angle-weight vanishes for points above every vertex. Unlike the
horizontal directions this is *not* per-edge: each edge contributes a step
`¼(sign(vᵢ₊₁−q).1 − sign(vᵢ−q).1)` (both endpoints below `q`), and these
telescope over the closed polygon. -/
lemma angleWeight_eq_zero_of_far_up (P : LatticePolygon) (q : Pt)
    (h : ∀ i, (P.vert i).2 < q.2) : angleWeight P q = 0 := by
  classical
  unfold angleWeight
  have key : ∀ i, latWeight (P.vert i - q) (P.vert (i + 1) - q)
      = ((Int.sign (P.vert (i + 1) - q).1 - Int.sign (P.vert i - q).1 : ℤ) : ℚ) / 4 := by
    intro i
    apply latWeight_eq_of_both_below
    · simp only [Prod.snd_sub]; have := h i; omega
    · simp only [Prod.snd_sub]; have := h (i + 1); omega
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.sum_div]
  have reindex : (∑ i, Int.sign (P.vert (i + 1) - q).1) = ∑ i, Int.sign (P.vert i - q).1 :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n)) (fun i => Int.sign (P.vert i - q).1)
  have hsum : (∑ i, ((Int.sign (P.vert (i + 1) - q).1 - Int.sign (P.vert i - q).1 : ℤ) : ℚ)) = 0 := by
    rw [← Int.cast_sum]
    norm_cast
    rw [Finset.sum_sub_distrib, reindex, sub_self]
  rw [hsum, zero_div]

/-- The angle-weight vanishes for points below every vertex (telescopes, via
`latWeight_eq_of_both_above`). -/
lemma angleWeight_eq_zero_of_far_down (P : LatticePolygon) (q : Pt)
    (h : ∀ i, q.2 < (P.vert i).2) : angleWeight P q = 0 := by
  classical
  unfold angleWeight
  have key : ∀ i, latWeight (P.vert i - q) (P.vert (i + 1) - q)
      = ((Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1 : ℤ) : ℚ) / 4 := by
    intro i
    apply latWeight_eq_of_both_above
    · simp only [Prod.snd_sub]; have := h i; omega
    · simp only [Prod.snd_sub]; have := h (i + 1); omega
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.sum_div]
  have reindex : (∑ i, Int.sign (P.vert (i + 1) - q).1) = ∑ i, Int.sign (P.vert i - q).1 :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n)) (fun i => Int.sign (P.vert i - q).1)
  have hsum : (∑ i, ((Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1 : ℤ) : ℚ)) = 0 := by
    rw [← Int.cast_sum]
    norm_cast
    rw [Finset.sum_sub_distrib, reindex, sub_self]
  rw [hsum, zero_div]

/-- If all vertices lie in `Box r`, the angle-weight vanishes outside `Box r`
(so the Step-1 box sum is over the whole support). -/
lemma angleWeight_zero_outside_box (P : LatticePolygon) (r : ℕ) (hr : ∀ i, P.vert i ∈ Box r)
    (q : Pt) (hq : q ∉ Box r) : angleWeight P q = 0 := by
  have hb : ∀ i, -(r : ℤ) ≤ (P.vert i).1 ∧ (P.vert i).1 ≤ r ∧
      -(r : ℤ) ≤ (P.vert i).2 ∧ (P.vert i).2 ≤ r := fun i => (mem_Box r (P.vert i)).mp (hr i)
  rw [mem_Box] at hq
  by_cases h1 : q.1 ≤ (r : ℤ)
  · by_cases h2 : -(r : ℤ) ≤ q.1
    · by_cases h3 : q.2 ≤ (r : ℤ)
      · exact angleWeight_eq_zero_of_far_down P q fun i => by have := hb i; omega
      · exact angleWeight_eq_zero_of_far_up P q fun i => by have := hb i; omega
    · exact angleWeight_eq_zero_of_far_left P q fun i => by have := hb i; omega
  · exact angleWeight_eq_zero_of_far_right P q fun i => by have := hb i; omega

/-- Every lattice polygon fits in some box (its vertices are finite). -/
theorem exists_box (P : LatticePolygon) : ∃ r : ℕ, ∀ i, P.vert i ∈ Box r := by
  classical
  refine ⟨Finset.univ.sup fun i => max (P.vert i).1.natAbs (P.vert i).2.natAbs, fun i => ?_⟩
  rw [mem_Box]
  have h := Finset.le_sup (f := fun i => max (P.vert i).1.natAbs (P.vert i).2.natAbs)
    (Finset.mem_univ i)
  simp only [Nat.max_le] at h
  omega

/-- **Step 1 in canonical form.** The shoelace area equals the lattice-wide
(finitely-supported) sum of the angle-weight, `∑ᶠ q, ŵ(q)`. Independent of any
box. This is exactly the quantity Step 3 evaluates to `I + B/2 − 1`. -/
theorem shoelace_eq_finsum (P : LatticePolygon) :
    P.shoelace = ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) := by
  obtain ⟨r, hr⟩ := exists_box P
  rw [shoelace_eq_totalWeight P r hr]
  congr 1
  rw [finsum_eq_finsetSum_of_support_subset (angleWeight P) (s := Box r) ?_]
  · rfl
  · intro q hq
    rw [Function.mem_support] at hq
    rw [Finset.mem_coe]
    by_contra hc
    exact hq (angleWeight_zero_outside_box P r hr q hc)

end Pick
