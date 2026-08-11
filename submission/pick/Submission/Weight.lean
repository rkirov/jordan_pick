import Submission.Defs

/-!
# The fractional lattice-point weight (count side, Step 1)

For the discrete count we cannot use the integer winding number: a boundary
lattice point must contribute a *fraction* (½ on an edge) for the sum to land on
`I + B/2 − 1`. We use `latWeight a b`, the signed winding contribution of the
directed edge `a → b` about the origin, counting crossings of the vertical axis
with half-weight on the axis. Values lie in `{-½, -¼, 0, ¼, ½}`.

Important: unlike `winding`, `latWeight (u-q) (v-q)` does **not** have finite
support as `q` ranges over ℤ² (the `±½` contributions of a slanted edge persist
to infinity in `y`). The per-edge identity therefore holds over a *box* `Box r`
large enough to contain the polygon, not over all of ℤ².

## Prior art

The fractional-weight count side here follows the discrete-angle-weight device of
Eisermann, *Formalizing Pick's Theorem, efficiently* (arXiv:2603.23095):
our `latWeight` is their `dang`, and `latWeightSum` (the box-sum, `∑_{Box r} latWeight`)
plays the role of their `Welp`. The per-edge identity `latWeightSum = trapezoidArea`
is proved independently here — we decompose the box by *columns*, whereas they use a
four-box partition with a reflection involution. The original content of this
repository is the *geometric* completion (the polygonal Jordan curve theorem and the
ear-clipping reduction), which their development leaves unproved (`sorry`).
-/

namespace Pick

/-- Integer cross product of lattice vectors. -/
def crossZ (a b : Pt) : ℤ := a.1 * b.2 - a.2 * b.1

/-- Fractional winding weight of the directed edge `a → b` about the origin. -/
def latWeight (a b : Pt) : ℚ :=
  (|Int.sign a.1 - Int.sign b.1| : ℚ) * (Int.sign (crossZ a b) : ℚ) / 4

@[simp] lemma crossZ_skew (a b : Pt) : crossZ b a = - crossZ a b := by unfold crossZ; ring

@[simp] lemma crossZ_self (a : Pt) : crossZ a a = 0 := by unfold crossZ; ring

/-- An edge with a vanishing endpoint difference has zero weight: `crossZ 0 b = 0`,
so `latWeight 0 b = 0`. At a vertex `q = vₖ` the two incident edges each have such a
zero argument, so `angleWeight P (vₖ)` only sees the non-incident edges. -/
@[simp] lemma latWeight_left_zero (b : Pt) : latWeight 0 b = 0 := by
  simp [latWeight, crossZ]

@[simp] lemma latWeight_right_zero (a : Pt) : latWeight a 0 = 0 := by
  simp [latWeight, crossZ]

/-- `latWeight` factors as `sign(crossZ)` (above/below the edge) times the column
weight `|sign a.1 − sign b.1|/4`. The per-point sum thus separates a crossing
direction from a column count. -/
lemma latWeight_eq_sign_mul (a b : Pt) :
    latWeight a b = (Int.sign (crossZ a b) : ℚ) * (|Int.sign a.1 - Int.sign b.1| : ℚ) / 4 := by
  unfold latWeight; ring

/-- When `q` lies on the edge's line (`crossZ (u−q) (v−q) = 0`), that edge contributes
zero weight. So for `q` on the interior of edge `i`, edge `i` drops out and the
remaining edges give the boundary half-weight. -/
lemma latWeight_eq_zero_of_crossZ_zero (a b : Pt) (h : crossZ a b = 0) :
    latWeight a b = 0 := by
  unfold latWeight; rw [h]; simp

/-- For a positive corner cross (`crossZ a b > 0`, a convex left turn), the weight is
the x-direction sign-difference over 4. With `crossZ < 0` it is its negative. These
package the per-vertex Hopf term `latWeight (vₖ₊₁−vₖ) (vₖ₋₁−vₖ)`. -/
lemma latWeight_of_crossZ_pos (a b : Pt) (h : 0 < crossZ a b) :
    latWeight a b = (|Int.sign a.1 - Int.sign b.1| : ℚ) / 4 := by
  unfold latWeight; rw [Int.sign_eq_one_of_pos h]; simp

/-- The cross product along an edge is affine in the test point `q`:
`crossZ (u−q) (v−q) = crossZ u v − q.1·(v.2−u.2) + q.2·(v.1−u.1)`. Its sign as
`q.2` varies (slope `v.1−u.1`) is what places `q` above or below the edge line. -/
lemma crossZ_sub_sub (u v q : Pt) :
    crossZ (u - q) (v - q) = crossZ u v - q.1 * (v.2 - u.2) + q.2 * (v.1 - u.1) := by
  unfold crossZ; simp only [Prod.fst_sub, Prod.snd_sub]; ring

/-- How `crossZ` shifts under a unit vertical step of both points: it changes by
`b.1 − a.1`. As the test point `q` moves up (so `a = vᵢ−q` moves down), this
governs when a `latWeight` term flips sign — the basis of the discrete
ray-casting / winding argument. -/
lemma crossZ_vshift (a b : Pt) :
    crossZ (a - (0, 1)) (b - (0, 1)) = crossZ a b + (b.1 - a.1) := by
  unfold crossZ
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The change in `latWeight` under a unit vertical step of both points: only the
`crossZ` sign can flip (the `x`-signs are unchanged), so the change is
`¼|sign a.1 − sign b.1| · (sign(crossZ + (b.1−a.1)) − sign crossZ)`. -/
lemma latWeight_vshift (a b : Pt) :
    latWeight (a - (0, 1)) (b - (0, 1)) - latWeight a b
      = ((|Int.sign a.1 - Int.sign b.1| : ℤ) : ℚ)
        * ((Int.sign (crossZ a b + (b.1 - a.1)) - Int.sign (crossZ a b) : ℤ) : ℚ) / 4 := by
  unfold latWeight
  rw [crossZ_vshift]
  have h1 : (a - (0, 1) : Pt).1 = a.1 := by simp [Prod.fst_sub]
  have h2 : (b - (0, 1) : Pt).1 = b.1 := by simp [Prod.fst_sub]
  rw [h1, h2]
  push_cast
  ring

/-- For an edge straddling the vertical line through `q` (opposite nonzero
`x`-signs), the vertical-step change is `½(sign(crossZ + (b.1−a.1)) − sign crossZ)` —
a clean `±1`/`0` crossing contribution. -/
lemma latWeight_vshift_of_opp (a b : Pt) (ha : a.1 < 0) (hb : 0 < b.1) :
    latWeight (a - (0, 1)) (b - (0, 1)) - latWeight a b
      = ((Int.sign (crossZ a b + (b.1 - a.1)) - Int.sign (crossZ a b) : ℤ) : ℚ) / 2 := by
  rw [latWeight_vshift, Int.sign_eq_neg_one_of_neg ha, Int.sign_eq_one_of_pos hb]
  push_cast
  ring

/-- The straddle case with the opposite orientation (`a.1 > 0`, `b.1 < 0`). -/
lemma latWeight_vshift_of_opp' (a b : Pt) (ha : 0 < a.1) (hb : b.1 < 0) :
    latWeight (a - (0, 1)) (b - (0, 1)) - latWeight a b
      = ((Int.sign (crossZ a b + (b.1 - a.1)) - Int.sign (crossZ a b) : ℤ) : ℚ) / 2 := by
  rw [latWeight_vshift, Int.sign_eq_one_of_pos ha, Int.sign_eq_neg_one_of_neg hb]
  push_cast
  ring

/-- On the bottom strip (`q.2 ≤ u.2+v.2−r−1`) of an edge whose endpoints lie in
`Box r` (so `u.2, v.2 ≤ r`), the cross product is negative: `q.2 < u.2` and
`q.2 < v.2`, so `q` is below the edge at both endpoints, hence below it
throughout. -/
lemma crossZ_neg_of_bottom_box (u v q : Pt) (r : ℕ) (huv : u.1 < v.1)
    (hu2 : u.2 ≤ r) (hv2 : v.2 ≤ r) (hcol1 : u.1 ≤ q.1) (hcol2 : q.1 ≤ v.1)
    (hrow : q.2 ≤ u.2 + v.2 - r - 1) :
    crossZ (u - q) (v - q) < 0 := by
  rw [crossZ_sub_sub]
  unfold crossZ
  have huq : (0 : ℤ) ≤ q.1 - u.1 := by omega
  have hqv : (0 : ℤ) ≤ v.1 - q.1 := by omega
  nlinarith [mul_nonneg huq (show (0 : ℤ) ≤ v.2 - q.2 - 1 by omega),
    mul_nonneg hqv (show (0 : ℤ) ≤ u.2 - q.2 - 1 by omega), huv]

/-- The weight is antisymmetric: reversing the edge negates it. -/
lemma latWeight_skew (a b : Pt) : latWeight b a = - latWeight a b := by
  unfold latWeight
  rw [crossZ_skew, Int.sign_neg]
  push_cast
  rw [abs_sub_comm]
  ring

/-- An edge whose endpoints lie on the same side of the vertical axis contributes
nothing. -/
lemma latWeight_eq_zero_of_sign_eq (a b : Pt) (h : Int.sign a.1 = Int.sign b.1) :
    latWeight a b = 0 := by
  unfold latWeight; rw [h]; simp only [sub_self, abs_zero, zero_mul, zero_div]

/-- `Int.sign` takes only the values `-1, 0, 1`. -/
lemma sign_trichotomy (x : ℤ) : Int.sign x = -1 ∨ Int.sign x = 0 ∨ Int.sign x = 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · exact Or.inl (Int.sign_eq_neg_one_of_neg h)
  · subst h; exact Or.inr (Or.inl Int.sign_zero)
  · exact Or.inr (Or.inr (Int.sign_eq_one_of_pos h))

/-- A genuine column crossing (endpoints on strictly opposite sides of the origin's
`x`) has column weight exactly `2` — the full `±½` contribution. -/
lemma abs_sign_diff_eq_two_of_opp (a b : ℤ) (h : (a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a)) :
    |Int.sign a - Int.sign b| = 2 := by
  rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rw [Int.sign_eq_neg_one_of_neg ha, Int.sign_eq_one_of_pos hb]; decide
  · rw [Int.sign_eq_neg_one_of_neg hb, Int.sign_eq_one_of_pos ha]; decide

/-- **Interior-column combinatorial core.** Three signs in `{-1,0,1}` with both `+1`
and `−1` present (an interior point's column is straddled by the vertices — possibly
with one vertex on the column) give cyclic sign-difference sum `|s₀−s₁| + |s₁−s₂| +
|s₂−s₀| = 4`. With `crossZ > 0` at every edge, `angleWeight` at an interior point is
`4/4 = 1`. -/
lemma sign_diff_abs_sum (s0 s1 s2 : ℤ) (h0 : s0 = -1 ∨ s0 = 0 ∨ s0 = 1)
    (h1 : s1 = -1 ∨ s1 = 0 ∨ s1 = 1) (h2 : s2 = -1 ∨ s2 = 0 ∨ s2 = 1)
    (hp : s0 = 1 ∨ s1 = 1 ∨ s2 = 1) (hn : s0 = -1 ∨ s1 = -1 ∨ s2 = -1) :
    |s0 - s1| + |s1 - s2| + |s2 - s0| = 4 := by
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl <;>
    first
      | decide
      | (rcases hp with h | h | h <;> rcases hn with h' | h' | h' <;> omega)

/-- **Crossing-count core.** Three indicators in `{0,1}` with both `0` and `1` present
(a horizontal line straddled by the vertices) give cyclic difference sum
`|i₀−i₁| + |i₁−i₂| + |i₂−i₀| = 2`. This is the "the line crosses the triangle twice"
fact, paired with the up/down balance to give `winding = 1` at an interior point. -/
lemma indicator_diff_abs_sum (i0 i1 i2 : ℤ) (h0 : i0 = 0 ∨ i0 = 1) (h1 : i1 = 0 ∨ i1 = 1)
    (h2 : i2 = 0 ∨ i2 = 1) (hz : i0 = 0 ∨ i1 = 0 ∨ i2 = 0) (ho : i0 = 1 ∨ i1 = 1 ∨ i2 = 1) :
    |i0 - i1| + |i1 - i2| + |i2 - i0| = 2 := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    first
      | decide
      | (rcases hz with h | h | h <;> rcases ho with h' | h' | h' <;> omega)

/-- **Hopf combinatorial core.** Three signs in `{-1,0,1}` with at least one `+1` and
at least one `-1` (the constraint from `d₀+d₁+d₂=0`, not all zero) satisfy
`|s₀+s₂| + |s₀+s₁| + |s₁+s₂| = 2`. This is the discrete "two vertical tangents" fact:
the per-vertex Hopf terms sum to `2/4 = 1/2 = n/2 − 1` for a triangle. -/
lemma sign_abs_sum (s0 s1 s2 : ℤ) (h0 : s0 = -1 ∨ s0 = 0 ∨ s0 = 1)
    (h1 : s1 = -1 ∨ s1 = 0 ∨ s1 = 1) (h2 : s2 = -1 ∨ s2 = 0 ∨ s2 = 1)
    (hp : s0 = 1 ∨ s1 = 1 ∨ s2 = 1) (hn : s0 = -1 ∨ s1 = -1 ∨ s2 = -1) :
    |s0 + s2| + |s0 + s1| + |s1 + s2| = 2 := by
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl <;>
    first
      | decide
      | (rcases hp with h | h | h <;> rcases hn with h' | h' | h' <;> omega)

/-- When both points are below the `x`-axis, the weight collapses to the
`x`-sign step `¼(sign b.1 − sign a.1)` (the sign of `crossZ` is forced in each
case). This is the key to the far-up/down vanishing of the angle-weight, which
telescopes over the closed polygon. -/
lemma latWeight_eq_of_both_below (a b : Pt) (ha : a.2 < 0) (hb : b.2 < 0) :
    latWeight a b = ((Int.sign b.1 - Int.sign a.1 : ℤ) : ℚ) / 4 := by
  unfold latWeight crossZ
  rcases lt_trichotomy a.1 0 with ha1 | ha1 | ha1 <;>
    rcases lt_trichotomy b.1 0 with hb1 | hb1 | hb1
  · rw [Int.sign_eq_neg_one_of_neg ha1, Int.sign_eq_neg_one_of_neg hb1]; norm_num
  · have hc : 0 < a.1 * b.2 - a.2 * b.1 := by nlinarith [mul_pos_of_neg_of_neg ha1 hb]
    rw [Int.sign_eq_neg_one_of_neg ha1, Int.sign_eq_zero_iff_zero.mpr hb1,
      Int.sign_eq_one_of_pos hc]; norm_num
  · have hc : 0 < a.1 * b.2 - a.2 * b.1 := by
      nlinarith [mul_pos_of_neg_of_neg ha1 hb, mul_neg_of_neg_of_pos ha hb1]
    rw [Int.sign_eq_neg_one_of_neg ha1, Int.sign_eq_one_of_pos hb1,
      Int.sign_eq_one_of_pos hc]; norm_num
  · have hc : a.1 * b.2 - a.2 * b.1 < 0 := by nlinarith [mul_pos_of_neg_of_neg ha hb1]
    rw [Int.sign_eq_zero_iff_zero.mpr ha1, Int.sign_eq_neg_one_of_neg hb1,
      Int.sign_eq_neg_one_of_neg hc]; norm_num
  · rw [Int.sign_eq_zero_iff_zero.mpr ha1, Int.sign_eq_zero_iff_zero.mpr hb1]; norm_num
  · have hc : 0 < a.1 * b.2 - a.2 * b.1 := by nlinarith [mul_neg_of_neg_of_pos ha hb1]
    rw [Int.sign_eq_zero_iff_zero.mpr ha1, Int.sign_eq_one_of_pos hb1,
      Int.sign_eq_one_of_pos hc]; norm_num
  · have hc : a.1 * b.2 - a.2 * b.1 < 0 := by
      nlinarith [mul_neg_of_pos_of_neg ha1 hb, mul_pos_of_neg_of_neg ha hb1]
    rw [Int.sign_eq_one_of_pos ha1, Int.sign_eq_neg_one_of_neg hb1,
      Int.sign_eq_neg_one_of_neg hc]; norm_num
  · have hc : a.1 * b.2 - a.2 * b.1 < 0 := by nlinarith [mul_neg_of_pos_of_neg ha1 hb]
    rw [Int.sign_eq_one_of_pos ha1, Int.sign_eq_zero_iff_zero.mpr hb1,
      Int.sign_eq_neg_one_of_neg hc]; norm_num
  · rw [Int.sign_eq_one_of_pos ha1, Int.sign_eq_one_of_pos hb1]; norm_num

/-- The box of lattice points with sup-norm `≤ r`. The per-edge weight identity
holds when summed over a box this large (with `r` at least the polygon bound),
because `latWeight` lacks finite support over all of ℤ². -/
noncomputable def Box (r : ℕ) : Finset Pt := Finset.Icc (-(r : ℤ), -(r : ℤ)) ((r : ℤ), (r : ℤ))

@[simp] lemma mem_Box (r : ℕ) (q : Pt) :
    q ∈ Box r ↔ -(r : ℤ) ≤ q.1 ∧ q.1 ≤ r ∧ -(r : ℤ) ≤ q.2 ∧ q.2 ≤ r := by
  unfold Box
  rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
  tauto

/-- Per-edge weighted lattice sum over `Box r`: the count-side analogue of one
trapezoid. -/
noncomputable def latWeightSum (u v : Pt) (r : ℕ) : ℚ := ∑ q ∈ Box r, latWeight (u - q) (v - q)

/-- `latWeightSum` is antisymmetric in the edge direction, matching `trapezoidArea`. -/
lemma latWeightSum_skew (u v : Pt) (r : ℕ) : latWeightSum v u r = - latWeightSum u v r := by
  unfold latWeightSum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun q _ => latWeight_skew (u - q) (v - q)

/-- A vertical edge (equal `x`-coordinates) has zero weight, matching
`trapezoidArea`. -/
lemma latWeightSum_eq_zero_of_fst_eq (u v : Pt) (r : ℕ) (h : u.1 = v.1) : latWeightSum u v r = 0 := by
  unfold latWeightSum
  refine Finset.sum_eq_zero fun q _ => latWeight_eq_zero_of_sign_eq _ _ ?_
  simp only [Prod.fst_sub, h]

/-- The weight is invariant under negating both arguments (point reflection
through the origin). -/
lemma latWeight_neg_neg (a b : Pt) : latWeight (-a) (-b) = latWeight a b := by
  simp only [latWeight, crossZ, Prod.fst_neg, Prod.snd_neg, Int.sign_neg, neg_mul_neg]
  have key : |(↑(-a.1.sign) : ℚ) - ↑(-b.1.sign)| = |(↑a.1.sign : ℚ) - ↑b.1.sign| := by
    push_cast
    rw [show (-(a.1.sign : ℚ)) - -(b.1.sign : ℚ) = -((a.1.sign : ℚ) - (b.1.sign : ℚ)) by ring,
      abs_neg]
  rw [key]

/-- Reflecting both points across the `x`-axis negates the weight. (Used to drop
the `u.2+v.2 ≥ 0` orientation assumption in the per-edge identity.) -/
lemma latWeight_yreflect (a b : Pt) :
    latWeight (a.1, -a.2) (b.1, -b.2) = -latWeight a b := by
  unfold latWeight crossZ
  dsimp only
  rw [show a.1 * -b.2 - -a.2 * b.1 = -(a.1 * b.2 - a.2 * b.1) by ring, Int.sign_neg]
  push_cast; ring

/-- A lattice point left of both endpoints' `x`-coordinates contributes nothing
(left box). -/
lemma latWeight_eq_zero_of_lt_fst (u v q : Pt) (hu : q.1 < u.1) (hv : q.1 < v.1) :
    latWeight (u - q) (v - q) = 0 := by
  apply latWeight_eq_zero_of_sign_eq
  simp only [Prod.fst_sub]
  rw [Int.sign_eq_one_of_pos (by omega), Int.sign_eq_one_of_pos (by omega)]

/-- A lattice point right of both endpoints' `x`-coordinates contributes nothing
(right box). -/
lemma latWeight_eq_zero_of_gt_fst (u v q : Pt) (hu : u.1 < q.1) (hv : v.1 < q.1) :
    latWeight (u - q) (v - q) = 0 := by
  apply latWeight_eq_zero_of_sign_eq
  simp only [Prod.fst_sub]
  rw [Int.sign_eq_neg_one_of_neg (by omega), Int.sign_eq_neg_one_of_neg (by omega)]

/-- A lattice point in an interior column (`u.1 < q.1 < v.1`) strictly below the
edge (`crossZ (u−q) (v−q) < 0`) has weight exactly `−½`. The bottom box is made
of such cells, so its sum is `−½ × (cell count)`. -/
lemma latWeight_interior_below (u v q : Pt) (h1 : u.1 < q.1) (h2 : q.1 < v.1)
    (h3 : crossZ (u - q) (v - q) < 0) : latWeight (u - q) (v - q) = -(1 / 2) := by
  unfold latWeight
  rw [Int.sign_eq_neg_one_of_neg h3]
  have e1 : (u - q).1.sign = -1 :=
    Int.sign_eq_neg_one_of_neg (by simp only [Prod.fst_sub]; omega)
  have e2 : (v - q).1.sign = 1 :=
    Int.sign_eq_one_of_pos (by simp only [Prod.fst_sub]; omega)
  rw [e1, e2]
  norm_num

/-- An interior column strictly above the edge (`crossZ (u−q) (v−q) > 0`) has
weight exactly `+½`. -/
lemma latWeight_interior_above (u v q : Pt) (h1 : u.1 < q.1) (h2 : q.1 < v.1)
    (h3 : 0 < crossZ (u - q) (v - q)) : latWeight (u - q) (v - q) = 1 / 2 := by
  unfold latWeight
  rw [Int.sign_eq_one_of_pos h3]
  have e1 : (u - q).1.sign = -1 :=
    Int.sign_eq_neg_one_of_neg (by simp only [Prod.fst_sub]; omega)
  have e2 : (v - q).1.sign = 1 :=
    Int.sign_eq_one_of_pos (by simp only [Prod.fst_sub]; omega)
  rw [e1, e2]
  norm_num

/-- The left boundary column (`q.1 = u.1`) below the edge has weight `−¼`. -/
lemma latWeight_boundary_left_below (u v q : Pt) (h1 : q.1 = u.1) (h2 : u.1 < v.1)
    (h3 : crossZ (u - q) (v - q) < 0) : latWeight (u - q) (v - q) = -(1 / 4) := by
  unfold latWeight
  rw [Int.sign_eq_neg_one_of_neg h3]
  have e1 : (u - q).1.sign = 0 :=
    Int.sign_eq_zero_iff_zero.mpr (by simp only [Prod.fst_sub]; omega)
  have e2 : (v - q).1.sign = 1 :=
    Int.sign_eq_one_of_pos (by simp only [Prod.fst_sub]; omega)
  rw [e1, e2]; norm_num

/-- The right boundary column (`q.1 = v.1`) below the edge has weight `−¼`. -/
lemma latWeight_boundary_right_below (u v q : Pt) (h1 : q.1 = v.1) (h2 : u.1 < v.1)
    (h3 : crossZ (u - q) (v - q) < 0) : latWeight (u - q) (v - q) = -(1 / 4) := by
  unfold latWeight
  rw [Int.sign_eq_neg_one_of_neg h3]
  have e1 : (u - q).1.sign = -1 :=
    Int.sign_eq_neg_one_of_neg (by simp only [Prod.fst_sub]; omega)
  have e2 : (v - q).1.sign = 0 :=
    Int.sign_eq_zero_iff_zero.mpr (by simp only [Prod.fst_sub]; omega)
  rw [e1, e2]; norm_num

/-- The left boundary column (`q.1 = u.1`) above the edge has weight `+¼`. -/
lemma latWeight_boundary_left_above (u v q : Pt) (h1 : q.1 = u.1) (h2 : u.1 < v.1)
    (h3 : 0 < crossZ (u - q) (v - q)) : latWeight (u - q) (v - q) = 1 / 4 := by
  unfold latWeight
  rw [Int.sign_eq_one_of_pos h3]
  have e1 : (u - q).1.sign = 0 :=
    Int.sign_eq_zero_iff_zero.mpr (by simp only [Prod.fst_sub]; omega)
  have e2 : (v - q).1.sign = 1 :=
    Int.sign_eq_one_of_pos (by simp only [Prod.fst_sub]; omega)
  rw [e1, e2]; norm_num

/-- The right boundary column (`q.1 = v.1`) above the edge has weight `+¼`. -/
lemma latWeight_boundary_right_above (u v q : Pt) (h1 : q.1 = v.1) (h2 : u.1 < v.1)
    (h3 : 0 < crossZ (u - q) (v - q)) : latWeight (u - q) (v - q) = 1 / 4 := by
  unfold latWeight
  rw [Int.sign_eq_one_of_pos h3]
  have e1 : (u - q).1.sign = -1 :=
    Int.sign_eq_neg_one_of_neg (by simp only [Prod.fst_sub]; omega)
  have e2 : (v - q).1.sign = 0 :=
    Int.sign_eq_zero_iff_zero.mpr (by simp only [Prod.fst_sub]; omega)
  rw [e1, e2]; norm_num

/-- The point-reflection `q ↦ u+v−q` pairs lattice points with opposite weight:
this is what makes the central "blue box" cancel in the per-edge identity. -/
lemma latWeight_involution (u v q : Pt) :
    latWeight (u - q) (v - q) + latWeight (u - (u + v - q)) (v - (u + v - q)) = 0 := by
  have e1 : u - (u + v - q) = -(v - q) := by abel
  have e2 : v - (u + v - q) = -(u - q) := by abel
  rw [e1, e2, latWeight_neg_neg, latWeight_skew (u - q) (v - q), add_neg_cancel]

/-- The weight at a fixed point of the reflection `σ q = u+v−q` is zero
(there `u−q = −(v−q)`, so the cross product vanishes). -/
lemma latWeight_eq_zero_of_fixed (u v q : Pt) (h : u + v - q = q) :
    latWeight (u - q) (v - q) = 0 := by
  have hua : u - q = -(v - q) := by linear_combination h
  rw [hua]
  have hc : crossZ (-(v - q)) (v - q) = 0 := by
    unfold crossZ; simp only [Prod.fst_neg, Prod.snd_neg]; ring
  unfold latWeight
  rw [hc, Int.sign_zero]
  simp

/-- The weight sum over any set invariant under the reflection `σ q = u+v−q`
vanishes (the blue-box cancellation, in general form). -/
lemma sum_latWeight_eq_zero_of_invariant (u v : Pt) (S : Finset Pt)
    (hS : ∀ q ∈ S, u + v - q ∈ S) :
    ∑ q ∈ S, latWeight (u - q) (v - q) = 0 := by
  refine Finset.sum_involution (fun q _ => u + v - q) (fun q _ => latWeight_involution u v q)
    (fun q _ hf heq => hf (latWeight_eq_zero_of_fixed u v q heq)) (fun q hq => hS q hq)
    (fun q _ => by abel)

/-- `latWeightSum` equals the weight sum over the asymmetric part `Box \ σ(Box)`: the
symmetric part (where the reflection `σ q = u+v−q` stays in the box) cancels. -/
lemma latWeightSum_eq_sum_asymm (u v : Pt) (r : ℕ) :
    latWeightSum u v r =
      ∑ q ∈ (Box r).filter (fun q => u + v - q ∉ Box r), latWeight (u - q) (v - q) := by
  classical
  have hinv : ∑ q ∈ (Box r).filter (fun q => u + v - q ∈ Box r), latWeight (u - q) (v - q) = 0 := by
    apply sum_latWeight_eq_zero_of_invariant
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    have hb : u + v - (u + v - q) = q := by abel
    exact ⟨hq.2, by rw [hb]; exact hq.1⟩
  unfold latWeightSum
  rw [← Finset.sum_filter_add_sum_filter_not (Box r) (fun q => u + v - q ∈ Box r), hinv, zero_add]

/-- For an edge with endpoints in `Box r` and `u.2+v.2 ≥ 0`, a middle-column
point is in the asymmetric region (`σq ∉ Box`) iff it is in the bottom strip
`q.2 ≤ u.2+v.2−r−1`. Pure box arithmetic. -/
lemma sigma_notMem_iff (u v q : Pt) (r : ℕ) (hu : u ∈ Box r) (hv : v ∈ Box r)
    (hq : q ∈ Box r) (hcol1 : u.1 ≤ q.1) (hcol2 : q.1 ≤ v.1) (hy : 0 ≤ u.2 + v.2) :
    u + v - q ∉ Box r ↔ q.2 ≤ u.2 + v.2 - r - 1 := by
  simp only [mem_Box] at hu hv hq ⊢
  have h1 : (u + v - q).1 = u.1 + v.1 - q.1 := by simp only [Prod.fst_sub, Prod.fst_add]
  have h2 : (u + v - q).2 = u.2 + v.2 - q.2 := by simp only [Prod.snd_sub, Prod.snd_add]
  rw [h1, h2]
  omega

/-- `latWeightSum` equals the weight sum over the explicit rectangle (middle columns ∩
bottom strip). Non-rectangle cells of the asymmetric region are either outside
the middle columns (weight 0) or excluded by `sigma_notMem_iff`. -/
lemma latWeightSum_eq_sum_rect (u v : Pt) (r : ℕ) (huv : u.1 < v.1)
    (hu : u ∈ Box r) (hv : v ∈ Box r) (hy : 0 ≤ u.2 + v.2) :
    latWeightSum u v r =
      ∑ q ∈ (Box r).filter (fun q => u.1 ≤ q.1 ∧ q.1 ≤ v.1 ∧ q.2 ≤ u.2 + v.2 - r - 1),
        latWeight (u - q) (v - q) := by
  classical
  rw [latWeightSum_eq_sum_asymm u v r]
  symm
  apply Finset.sum_subset
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    obtain ⟨hqbox, hm1, hm2, hbot⟩ := hq
    exact ⟨hqbox, (sigma_notMem_iff u v q r hu hv hqbox hm1 hm2 hy).mpr hbot⟩
  · intro q hqasymm hqnotrect
    rw [Finset.mem_filter] at hqasymm
    obtain ⟨hqbox, hsig⟩ := hqasymm
    rw [Finset.mem_filter, not_and] at hqnotrect
    have hnp := hqnotrect hqbox
    by_cases hm1 : u.1 ≤ q.1
    · by_cases hm2 : q.1 ≤ v.1
      · exfalso
        rw [sigma_notMem_iff u v q r hu hv hqbox hm1 hm2 hy] at hsig
        exact hnp ⟨hm1, hm2, hsig⟩
      · exact latWeight_eq_zero_of_gt_fst u v q (by omega) (by omega)
    · exact latWeight_eq_zero_of_lt_fst u v q (by omega) (by omega)

/-- The rectangle filter set is exactly the lattice box
`[u.1, v.1] × [−r, u.2+v.2−r−1]` (the extra `Box r` bounds are implied since the
vertices lie in the box). -/
lemma rect_eq_Icc (u v : Pt) (r : ℕ) (hu : u ∈ Box r) (hv : v ∈ Box r) (_ : 0 ≤ u.2 + v.2) :
    (Box r).filter (fun q => u.1 ≤ q.1 ∧ q.1 ≤ v.1 ∧ q.2 ≤ u.2 + v.2 - r - 1)
      = Finset.Icc (u.1, -(r : ℤ)) (v.1, u.2 + v.2 - r - 1) := by
  simp only [mem_Box] at hu hv
  ext q
  simp only [Finset.mem_filter, mem_Box, Finset.mem_Icc, Prod.le_def]
  omega

/-- An interior column of the rectangle sums to `−(u.2+v.2)/2`: every cell has
weight `−½` (below the edge), and there are `u.2+v.2` rows. -/
lemma col_sum_interior (u v : Pt) (r : ℕ) (x : ℤ) (huv : u.1 < v.1)
    (hu2 : u.2 ≤ (r : ℤ)) (hv2 : v.2 ≤ (r : ℤ)) (hy : 0 ≤ u.2 + v.2)
    (hx1 : u.1 < x) (hx2 : x < v.1) :
    ∑ y ∈ Finset.Icc (-(r : ℤ)) (u.2 + v.2 - r - 1), latWeight (u - (x, y)) (v - (x, y))
      = -(((u.2 + v.2 : ℤ) : ℚ)) / 2 := by
  have hconst : ∀ y ∈ Finset.Icc (-(r : ℤ)) (u.2 + v.2 - r - 1),
      latWeight (u - (x, y)) (v - (x, y)) = -(1 / 2) := by
    intro y hy'
    rw [Finset.mem_Icc] at hy'
    exact latWeight_interior_below u v (x, y) hx1 hx2
      (crossZ_neg_of_bottom_box u v (x, y) r huv hu2 hv2 (le_of_lt hx1) (le_of_lt hx2) hy'.2)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  have hcard : ((u.2 + v.2 - r - 1 + 1 - -(r : ℤ)).toNat : ℚ) = ((u.2 + v.2 : ℤ) : ℚ) := by
    have h0 : u.2 + v.2 - r - 1 + 1 - -(r : ℤ) = u.2 + v.2 := by ring
    rw [h0]
    exact_mod_cast Int.toNat_of_nonneg hy
  rw [hcard]; ring

/-- The left boundary column `x = u.1` sums to `−(u.2+v.2)/4`. -/
lemma col_sum_boundary_left (u v : Pt) (r : ℕ) (huv : u.1 < v.1)
    (hu2 : u.2 ≤ (r : ℤ)) (hv2 : v.2 ≤ (r : ℤ)) (hy : 0 ≤ u.2 + v.2) :
    ∑ y ∈ Finset.Icc (-(r : ℤ)) (u.2 + v.2 - r - 1), latWeight (u - (u.1, y)) (v - (u.1, y))
      = -(((u.2 + v.2 : ℤ) : ℚ)) / 4 := by
  have hconst : ∀ y ∈ Finset.Icc (-(r : ℤ)) (u.2 + v.2 - r - 1),
      latWeight (u - (u.1, y)) (v - (u.1, y)) = -(1 / 4) := by
    intro y hy'
    rw [Finset.mem_Icc] at hy'
    exact latWeight_boundary_left_below u v (u.1, y) rfl huv
      (crossZ_neg_of_bottom_box u v (u.1, y) r huv hu2 hv2 (le_refl u.1) (le_of_lt huv) hy'.2)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  have hcard : ((u.2 + v.2 - r - 1 + 1 - -(r : ℤ)).toNat : ℚ) = ((u.2 + v.2 : ℤ) : ℚ) := by
    have h0 : u.2 + v.2 - r - 1 + 1 - -(r : ℤ) = u.2 + v.2 := by ring
    rw [h0]; exact_mod_cast Int.toNat_of_nonneg hy
  rw [hcard]; ring

/-- The right boundary column `x = v.1` sums to `−(u.2+v.2)/4`. -/
lemma col_sum_boundary_right (u v : Pt) (r : ℕ) (huv : u.1 < v.1)
    (hu2 : u.2 ≤ (r : ℤ)) (hv2 : v.2 ≤ (r : ℤ)) (hy : 0 ≤ u.2 + v.2) :
    ∑ y ∈ Finset.Icc (-(r : ℤ)) (u.2 + v.2 - r - 1), latWeight (u - (v.1, y)) (v - (v.1, y))
      = -(((u.2 + v.2 : ℤ) : ℚ)) / 4 := by
  have hconst : ∀ y ∈ Finset.Icc (-(r : ℤ)) (u.2 + v.2 - r - 1),
      latWeight (u - (v.1, y)) (v - (v.1, y)) = -(1 / 4) := by
    intro y hy'
    rw [Finset.mem_Icc] at hy'
    exact latWeight_boundary_right_below u v (v.1, y) rfl huv
      (crossZ_neg_of_bottom_box u v (v.1, y) r huv hu2 hv2 (le_of_lt huv) (le_refl v.1) hy'.2)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  have hcard : ((u.2 + v.2 - r - 1 + 1 - -(r : ℤ)).toNat : ℚ) = ((u.2 + v.2 : ℤ) : ℚ) := by
    have h0 : u.2 + v.2 - r - 1 + 1 - -(r : ℤ) = u.2 + v.2 := by ring
    rw [h0]; exact_mod_cast Int.toNat_of_nonneg hy
  rw [hcard]; ring

/-- **Per-edge identity, base case** (`u.1 < v.1`, `u.2+v.2 ≥ 0`, vertices in the
box): the lattice-point weight sum equals the trapezoid value
`−(u.2+v.2)(v.1−u.1)/2`. Assembles the three column sums over the rectangle. -/
lemma latWeightSum_eq_trapezoid_base (u v : Pt) (r : ℕ) (huv : u.1 < v.1)
    (hu : u ∈ Box r) (hv : v ∈ Box r) (hy : 0 ≤ u.2 + v.2) :
    latWeightSum u v r = -(((u.2 + v.2) * (v.1 - u.1) : ℤ) : ℚ) / 2 := by
  have hu2 : u.2 ≤ (r : ℤ) := ((mem_Box r u).mp hu).2.2.2
  have hv2 : v.2 ≤ (r : ℤ) := ((mem_Box r v).mp hv).2.2.2
  rw [latWeightSum_eq_sum_rect u v r huv hu hv hy, rect_eq_Icc u v r hu hv hy,
    ← Finset.Icc_product_Icc, Finset.sum_product]
  have hsplit : Finset.Icc u.1 v.1 = insert u.1 (insert v.1 (Finset.Ioo u.1 v.1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]; omega
  have hni2 : v.1 ∉ Finset.Ioo u.1 v.1 := by simp [Finset.mem_Ioo]
  have hni1 : u.1 ∉ insert v.1 (Finset.Ioo u.1 v.1) := by
    simp only [Finset.mem_insert, Finset.mem_Ioo]; omega
  rw [hsplit, Finset.sum_insert hni1, Finset.sum_insert hni2,
    col_sum_boundary_left u v r huv hu2 hv2 hy, col_sum_boundary_right u v r huv hu2 hv2 hy,
    Finset.sum_congr rfl (fun x hx => col_sum_interior u v r x huv hu2 hv2 hy
      (Finset.mem_Ioo.mp hx).1 (Finset.mem_Ioo.mp hx).2),
    Finset.sum_const, Int.card_Ioo, nsmul_eq_mul]
  have hcard : (((v.1 - u.1 - 1).toNat : ℚ)) = ((v.1 - u.1 - 1 : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [hcard]
  push_cast
  ring

/-- Reflecting an edge across the `x`-axis negates `latWeightSum` (reindex the box sum by
`ρ q = (q.1, −q.2)`, which preserves the box). Used to drop the `u.2+v.2 ≥ 0`
assumption in the per-edge identity. -/
lemma latWeightSum_yreflect (u v : Pt) (r : ℕ) :
    latWeightSum (u.1, -u.2) (v.1, -v.2) r = -latWeightSum u v r := by
  unfold latWeightSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun q => (q.1, -q.2)) (fun q => (q.1, -q.2)) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [mem_Box] at ha ⊢; omega
  · intro a ha; simp only [mem_Box] at ha ⊢; omega
  · intro a _; simp
  · intro a _; simp
  · intro a _
    have e1 : ((u.1, -u.2) : Pt) - a = ((u - (a.1, -a.2)).1, -(u - (a.1, -a.2)).2) := by
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]; exact ⟨trivial, by omega⟩
    have e2 : ((v.1, -v.2) : Pt) - a = ((v - (a.1, -a.2)).1, -(v - (a.1, -a.2)).2) := by
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]; exact ⟨trivial, by omega⟩
    rw [e1, e2, latWeight_yreflect]

/-- When both points are above the `x`-axis, the weight is `¼(sign a.1 − sign
b.1)` (by `y`-reflection of `latWeight_eq_of_both_below`). -/
lemma latWeight_eq_of_both_above (a b : Pt) (ha : 0 < a.2) (hb : 0 < b.2) :
    latWeight a b = ((Int.sign a.1 - Int.sign b.1 : ℤ) : ℚ) / 4 := by
  have hbelow := latWeight_eq_of_both_below (a.1, -a.2) (b.1, -b.2)
    (by show (-a.2 : ℤ) < 0; omega) (by show (-b.2 : ℤ) < 0; omega)
  rw [latWeight_yreflect] at hbelow
  dsimp only at hbelow
  push_cast at hbelow ⊢
  linarith

/-- Per-edge identity (`u.1 < v.1`, any orientation): the weight sum equals the
trapezoid value. The `u.2+v.2 < 0` case follows from the base case by the
`y`-reflection (`latWeightSum_yreflect`). -/
lemma latWeightSum_eq_trapezoid_lt (u v : Pt) (r : ℕ) (huv : u.1 < v.1)
    (hu : u ∈ Box r) (hv : v ∈ Box r) :
    latWeightSum u v r = -(((u.2 + v.2) * (v.1 - u.1) : ℤ) : ℚ) / 2 := by
  by_cases hy : 0 ≤ u.2 + v.2
  · exact latWeightSum_eq_trapezoid_base u v r huv hu hv hy
  · have hρu : (u.1, -u.2) ∈ Box r := by simp only [mem_Box] at hu ⊢; omega
    have hρv : (v.1, -v.2) ∈ Box r := by simp only [mem_Box] at hv ⊢; omega
    have hb := latWeightSum_eq_trapezoid_base (u.1, -u.2) (v.1, -v.2) r huv hρu hρv
      (by show (0 : ℤ) ≤ -u.2 + -v.2; omega)
    rw [latWeightSum_yreflect] at hb
    dsimp only at hb
    push_cast at hb ⊢
    linarith

/-- **Per-edge identity** (all cases): for an edge with endpoints in the box, the
lattice-point weight sum equals the trapezoid value `−(u.2+v.2)(v.1−u.1)/2`. -/
lemma latWeightSum_eq_trapezoid (u v : Pt) (r : ℕ) (hu : u ∈ Box r) (hv : v ∈ Box r) :
    latWeightSum u v r = -(((u.2 + v.2) * (v.1 - u.1) : ℤ) : ℚ) / 2 := by
  rcases lt_trichotomy u.1 v.1 with h | h | h
  · exact latWeightSum_eq_trapezoid_lt u v r h hu hv
  · rw [latWeightSum_eq_zero_of_fst_eq u v r h]
    rw [show v.1 - u.1 = 0 by omega]; simp
  · rw [latWeightSum_skew v u r, latWeightSum_eq_trapezoid_lt v u r h hv hu]
    push_cast; ring

end Pick
