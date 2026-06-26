import Top100.PicksTheorem.Jordan
import Top100.PicksTheorem.PerEdge

/-!
# Pick's theorem: the assembled reduction

This capstone combines the verified pieces into the tightest statement of what
remains for the full geometric Pick's theorem. The algebraic half
(`shoelace = ∑ᶠ ŵ`, Step 1) is **complete and wired in here**; the master
assembly (`pick_of_hypotheses`, Step 2 structure) is complete; so `pick` reduces
to exactly three named ingredients:

* **`h01`** — `winding ∈ {0,1}` (the polygonal Jordan curve theorem);
* **`hgreen`** — `∫∫ winding = shoelace` (Green's theorem; Jordan-free analysis);
* **`hcount`** — `∑ᶠ ŵ = I + B/2 − 1` (the lattice-point count classification;
  needs the boundary angle-sum / Hopf).

`pick_of_three` proves the full geometric statement from these three, sorry-free.
-/

namespace Pick

open LatticePolygon

/-- **Pick's theorem from its three remaining ingredients** (with the completed
Step 1 `shoelace = ∑ᶠ ŵ` already incorporated). Given `winding ∈ {0,1}`, Green's
`∫∫ winding = shoelace`, and the count classification `∑ᶠ ŵ = I + B/2 − 1`, the
geometric area formula holds. -/
theorem pick_of_three (P : LatticePolygon)
    (h01 : ∀ q, P.winding q = 0 ∨ P.winding q = 1)
    (hgreen : ∫ q, (P.winding q : ℝ) = P.shoelace)
    (hcount : ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_hypotheses P h01 hgreen (by rw [shoelace_eq_finsum]; exact hcount)

/-- **Pick's theorem from its TWO remaining ingredients.** Green's theorem
(`hgreen : ∫∫ winding = shoelace`) is now **discharged** by `greens_theorem`
(proved Jordan-free, axiom-clean), together with the completed Step 1
(`shoelace = ∑ᶠ ŵ`). So `pick` reduces to exactly two named ingredients:

* **`h01`** — `winding ∈ {0,1}` (the polygonal Jordan curve theorem);
* **`hcount`** — `∑ᶠ ŵ = I + B/2 − 1` (the lattice-point count classification). -/
theorem pick_of_two (P : LatticePolygon)
    (h01 : ∀ q, P.winding q = 0 ∨ P.winding q = 1)
    (hcount : ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_three P h01 (greens_theorem P) hcount

/-- **Pick's theorem from the two ingredients, with the Jordan hypothesis only
needed a.e.** Green is discharged by `greens_theorem`; the Jordan crux `h01` is
weakened to hold almost everywhere (the boundary is null), which is what the
triangle base case + ear-clipping actually produce. -/
theorem pick_of_two_ae (P : LatticePolygon)
    (h01 : ∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1)
    (hcount : ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_hypotheses_ae P h01 (greens_theorem P) (by rw [shoelace_eq_finsum]; exact hcount)

/-- **Pick's theorem for a triangle, from the count alone.** The Jordan ingredient
is now fully discharged for triangles by `triangle_h01_ae`, so `pick` (for `n = 3`)
follows from just the lattice-point count `hcount`. Green's theorem is already wired
in. This isolates exactly what remains for the triangle base case: the Hopf
angle-sum count. -/
theorem pick_triangle (P : LatticePolygon) (hP : P.IsSimple) (hn : P.n = 3)
    (horient : P.PositivelyOriented)
    (hcount : ((∑ᶠ q, angleWeight P q : ℚ) : ℝ) = (P.I : ℝ) + (P.B : ℝ) / 2 - 1) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_two_ae P (triangle_h01_ae P hP hn horient) hcount

/-- **Angle-weight at a vertex (triangle).** At `q = vₖ` the two incident edges have
a zero `latWeight` argument, so `angleWeight P (vₖ)` reduces to the single opposite
edge `vₖ₊₁ → vₖ₋₁` viewed from `vₖ`. This is the per-vertex term of the Hopf count. -/
lemma angleWeight_vertex_triangle (P : LatticePolygon) (hn : P.n = 3) (k : ZMod P.n) :
    angleWeight P (P.vert k) =
      latWeight (P.vert (k + 1) - P.vert k) (P.vert (k - 1) - P.vert k) := by
  unfold angleWeight
  obtain ⟨n, pos, vert⟩ := P
  subst hn
  rw [zmod3_univ_eq_triple k, Finset.sum_insert (zmod3_sub_one_notMem k),
    Finset.sum_insert (zmod3_notMem_singleton k), Finset.sum_singleton,
    show ((k - 1) + 1) = k from by ring,
    show ((k + 1) + 1) = k - 1 from zmod3_add_one_add_one k]
  simp

/-- `toReal` is subtraction-linear. -/
lemma toReal_sub (a b : Pt) : toReal (a - b) = toReal a - toReal b := by
  unfold toReal
  simp [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]

/-- Sum over `ZMod P.n` with `P.n = 3` expands to three terms. -/
lemma sum_zmodPn {M : Type*} [AddCommMonoid M] (P : LatticePolygon) (hn : P.n = 3)
    (f : ZMod P.n → M) : (∑ k, f k) = f 0 + f 1 + f 2 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact sum_zmod3 f

/-- The six cyclic index identities in `ZMod 3`. -/
lemma zmod3_consts : ((0 : ZMod 3) + 1 = 1) ∧ ((1 : ZMod 3) + 1 = 2) ∧ ((2 : ZMod 3) + 1 = 0) ∧
    ((0 : ZMod 3) - 1 = 2) ∧ ((1 : ZMod 3) - 1 = 0) ∧ ((2 : ZMod 3) - 1 = 1) := by decide

/-- Same, transported to `ZMod P.n` for `P.n = 3`. -/
lemma zmodPn_idx (P : LatticePolygon) (hn : P.n = 3) :
    ((0 : ZMod P.n) + 1 = 1) ∧ ((1 : ZMod P.n) + 1 = 2) ∧ ((2 : ZMod P.n) + 1 = 0) ∧
    ((0 : ZMod P.n) - 1 = 2) ∧ ((1 : ZMod P.n) - 1 = 0) ∧ ((2 : ZMod P.n) - 1 = 1) := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_consts

lemma zmod3_cases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide

lemma zmodPn_cases (P : LatticePolygon) (hn : P.n = 3) (j : ZMod P.n) :
    j = 0 ∨ j = 1 ∨ j = 2 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_cases j

/-- **Positive corner cross at every triangle vertex** (integer version). The corner
cross `crossZ (vₖ₊₁−vₖ) (vₖ₋₁−vₖ)` equals `2·shoelace > 0`, so each vertex is a convex
left turn. This pins the sign in the per-vertex Hopf term. -/
lemma crossZ_vertex_pos (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented)
    (k : ZMod P.n) :
    0 < crossZ (P.vert (k + 1) - P.vert k) (P.vert (k - 1) - P.vert k) := by
  have hs : (0 : ℝ) < P.shoelace := horient
  have h1 : cross (toReal (P.vert (k + 1) - P.vert k)) (toReal (P.vert (k - 1) - P.vert k))
      = 2 * P.shoelace := by
    rw [toReal_sub, toReal_sub,
      cross_corner_cycle (toReal (P.vert (k - 1))) (toReal (P.vert k)) (toReal (P.vert (k + 1)))]
    exact corner_cross_base_eq_two_shoelace P hn k
  rw [cross_toReal_int] at h1
  have hpos : (0 : ℝ) < (((P.vert (k + 1) - P.vert k).1 * (P.vert (k - 1) - P.vert k).2
      - (P.vert (k + 1) - P.vert k).2 * (P.vert (k - 1) - P.vert k).1 : ℤ) : ℝ) := by
    rw [h1]; linarith
  show 0 < (P.vert (k + 1) - P.vert k).1 * (P.vert (k - 1) - P.vert k).2
      - (P.vert (k + 1) - P.vert k).2 * (P.vert (k - 1) - P.vert k).1
  exact_mod_cast hpos

/-- **Per-vertex Hopf term (triangle).** `angleWeight` at vertex `vₖ` is the x-direction
sign-difference of its two incident edges, over 4. Summing over the three vertices
should give `n/2 − 1 = 1/2` (the Hopf turning); that sum reduces to the combinatorial
identity `∑_k |sign-diff| = 2`. -/
lemma angleWeight_vertex_eq (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (k : ZMod P.n) :
    angleWeight P (P.vert k) =
      (|Int.sign (P.vert (k + 1) - P.vert k).1
        - Int.sign (P.vert (k - 1) - P.vert k).1| : ℚ) / 4 := by
  rw [angleWeight_vertex_triangle P hn k,
    latWeight_of_crossZ_pos _ _ (crossZ_vertex_pos P hn horient k)]

/-- Per-vertex Hopf term in clean form: `|sign dₖ + sign dₖ₋₁| / 4`, where
`dₖ = (vertₖ₊₁ − vertₖ).1`. (Uses `sign(−x) = −sign x` to fold the incoming edge.) -/
lemma angleWeight_vertex_g (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented)
    (k : ZMod P.n) :
    angleWeight P (P.vert k) = (|Int.sign ((P.vert (k + 1)).1 - (P.vert k).1)
      + Int.sign ((P.vert k).1 - (P.vert (k - 1)).1)| : ℚ) / 4 := by
  rw [angleWeight_vertex_eq P hn horient k]
  have hA : (P.vert (k + 1) - P.vert k).1.sign = ((P.vert (k + 1)).1 - (P.vert k).1).sign := by
    rw [Prod.fst_sub]
  have hB : (P.vert (k - 1) - P.vert k).1.sign = -((P.vert k).1 - (P.vert (k - 1)).1).sign := by
    rw [Prod.fst_sub,
      show (P.vert (k - 1)).1 - (P.vert k).1 = -((P.vert k).1 - (P.vert (k - 1)).1) from by ring,
      Int.sign_neg]
  have harg : ((P.vert (k + 1) - P.vert k).1.sign : ℚ) - (P.vert (k - 1) - P.vert k).1.sign
      = (((P.vert (k + 1)).1 - (P.vert k).1).sign : ℚ)
        + ((P.vert k).1 - (P.vert (k - 1)).1).sign := by
    rw [hA, hB]; push_cast; ring
  rw [harg]

/-- The x-differences `dₖ = (vertₖ₊₁ − vertₖ).1` sum to `0` around the closed polygon
(telescoping). Supplies the sign constraint for the Hopf vertex-sum. -/
lemma sum_x_diff_zero (P : LatticePolygon) :
    (∑ k, ((P.vert (k + 1)).1 - (P.vert k).1)) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod P.n))
    (fun k => (P.vert (k + 1)).1) (fun k => (P.vert k).1) (fun _ => rfl)

/-- When every corner cross `crossZ(vᵢ−q, vᵢ₊₁−q)` is positive (a point that sees the
whole boundary CCW — an interior point), `angleWeight P q` is `(∑ column-weights)/4`,
each `latWeight` being just its column weight. -/
lemma angleWeight_eq_of_crossZ_pos (P : LatticePolygon) (q : Pt)
    (h : ∀ i, 0 < crossZ (P.vert i - q) (P.vert (i + 1) - q)) :
    angleWeight P q
      = (↑(∑ i, |Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1|) : ℚ) / 4 := by
  unfold angleWeight
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [latWeight_eq_sign_mul, Int.sign_eq_one_of_pos (h i)]
  push_cast
  ring

/-- General per-point form: `angleWeight P q = (∑ᵢ sign(crossZ_i)·column-weight_i)/4`.
The basis for every per-point classification (interior, edge, exterior). -/
lemma angleWeight_eq_sum (P : LatticePolygon) (q : Pt) :
    angleWeight P q = (∑ i, (Int.sign (crossZ (P.vert i - q) (P.vert (i + 1) - q)) : ℚ)
      * (|Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1| : ℚ)) / 4 := by
  unfold angleWeight
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => latWeight_eq_sign_mul _ _)

/-- **Interior classification (triangle).** If `q` sees every edge CCW
(`crossZ(vᵢ−q, vᵢ₊₁−q) > 0` for all `i`) and its column is straddled (some vertex
strictly left, some strictly right), then `angleWeight P q = 1`. This is the interior
contribution of `hcount`. -/
lemma angleWeight_interior_triangle (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (hcross : ∀ i, 0 < crossZ (P.vert i - q) (P.vert (i + 1) - q))
    (hsp : ∃ i, 0 < (P.vert i - q).1) (hsn : ∃ i, (P.vert i - q).1 < 0) :
    angleWeight P q = 1 := by
  rw [angleWeight_eq_of_crossZ_pos P q hcross]
  obtain ⟨e1, e2, e3, _, _, _⟩ := zmodPn_idx P hn
  obtain ⟨ip, hip⟩ := hsp
  obtain ⟨iN, hiN⟩ := hsn
  have hp : Int.sign (P.vert 0 - q).1 = 1 ∨ Int.sign (P.vert 1 - q).1 = 1
      ∨ Int.sign (P.vert 2 - q).1 = 1 := by
    rcases zmodPn_cases P hn ip with h | h | h <;> subst h
    · exact Or.inl (Int.sign_eq_one_of_pos hip)
    · exact Or.inr (Or.inl (Int.sign_eq_one_of_pos hip))
    · exact Or.inr (Or.inr (Int.sign_eq_one_of_pos hip))
  have hm : Int.sign (P.vert 0 - q).1 = -1 ∨ Int.sign (P.vert 1 - q).1 = -1
      ∨ Int.sign (P.vert 2 - q).1 = -1 := by
    rcases zmodPn_cases P hn iN with h | h | h <;> subst h
    · exact Or.inl (Int.sign_eq_neg_one_of_neg hiN)
    · exact Or.inr (Or.inl (Int.sign_eq_neg_one_of_neg hiN))
    · exact Or.inr (Or.inr (Int.sign_eq_neg_one_of_neg hiN))
  have hsum := sign_diff_abs_sum _ _ _ (sign_trichotomy (P.vert 0 - q).1)
    (sign_trichotomy (P.vert 1 - q).1) (sign_trichotomy (P.vert 2 - q).1) hp hm
  rw [sum_zmodPn P hn (fun i => |Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1|),
    e1, e2, e3, hsum]
  norm_num

/-- The total column weight of a triangle around a point with a straddled column is
`4` (the cyclic sign-difference sum). Reused by both the interior and edge
classifications. -/
lemma triangle_columnWeight_sum (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (hsp : ∃ i, 0 < (P.vert i - q).1) (hsn : ∃ i, (P.vert i - q).1 < 0) :
    (∑ i, |Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1|) = 4 := by
  obtain ⟨e1, e2, e3, _, _, _⟩ := zmodPn_idx P hn
  obtain ⟨ip, hip⟩ := hsp
  obtain ⟨iN, hiN⟩ := hsn
  have hp : Int.sign (P.vert 0 - q).1 = 1 ∨ Int.sign (P.vert 1 - q).1 = 1
      ∨ Int.sign (P.vert 2 - q).1 = 1 := by
    rcases zmodPn_cases P hn ip with h | h | h <;> subst h
    · exact Or.inl (Int.sign_eq_one_of_pos hip)
    · exact Or.inr (Or.inl (Int.sign_eq_one_of_pos hip))
    · exact Or.inr (Or.inr (Int.sign_eq_one_of_pos hip))
  have hm : Int.sign (P.vert 0 - q).1 = -1 ∨ Int.sign (P.vert 1 - q).1 = -1
      ∨ Int.sign (P.vert 2 - q).1 = -1 := by
    rcases zmodPn_cases P hn iN with h | h | h <;> subst h
    · exact Or.inl (Int.sign_eq_neg_one_of_neg hiN)
    · exact Or.inr (Or.inl (Int.sign_eq_neg_one_of_neg hiN))
    · exact Or.inr (Or.inr (Int.sign_eq_neg_one_of_neg hiN))
  rw [sum_zmodPn P hn (fun i => |Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1|),
    e1, e2, e3]
  exact sign_diff_abs_sum _ _ _ (sign_trichotomy (P.vert 0 - q).1)
    (sign_trichotomy (P.vert 1 - q).1) (sign_trichotomy (P.vert 2 - q).1) hp hm

/-- **Edge classification (triangle).** If `q` lies on the line of edge `j`
(`crossZ_j = 0`, a genuine column crossing there) and sees the other two edges CCW,
with a straddled column, then `angleWeight P q = ½`. The on-edge term drops, leaving
column weight `4 − 2 = 2`, i.e. `2/4 = ½`. This is the edge contribution of `hcount`. -/
lemma angleWeight_edge_triangle (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (j : ZMod P.n)
    (hj : crossZ (P.vert j - q) (P.vert (j + 1) - q) = 0)
    (hi : ∀ i, i ≠ j → 0 < crossZ (P.vert i - q) (P.vert (i + 1) - q))
    (hcwj : |Int.sign (P.vert j - q).1 - Int.sign (P.vert (j + 1) - q).1| = 2)
    (hsp : ∃ i, 0 < (P.vert i - q).1) (hsn : ∃ i, (P.vert i - q).1 < 0) :
    angleWeight P q = 1 / 2 := by
  have hsum4 := triangle_columnWeight_sum P hn q hsp hsn
  rw [angleWeight_eq_sum, show (1 : ℚ) / 2 = 2 / 4 from by norm_num]
  congr 1
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), hj, Int.sign_zero,
    Int.cast_zero, zero_mul, zero_add]
  have step : ∀ i ∈ Finset.univ.erase j,
      (Int.sign (crossZ (P.vert i - q) (P.vert (i + 1) - q)) : ℚ)
        * (|Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1| : ℚ)
      = (|Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1| : ℚ) := fun i hmem => by
    rw [Int.sign_eq_one_of_pos (hi i (Finset.ne_of_mem_erase hmem)), Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl step]
  simp only [← Int.cast_sub, ← Int.cast_abs, ← Int.cast_sum]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hsum4, hcwj]
  norm_num

/-- **Exterior classification (triangle).** If `q` is on the wrong side of edge `k`
(`crossZ_k < 0`, a column crossing there) but sees the other two edges CCW, with a
straddled column, then `angleWeight P q = 0`. The wrong-side term contributes `−2`,
the rest `+2`: `(4 − 2·2)/4 = 0`. This is the (near) exterior contribution of
`hcount`. -/
lemma angleWeight_exterior_triangle (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0)
    (hi : ∀ i, i ≠ k → 0 < crossZ (P.vert i - q) (P.vert (i + 1) - q))
    (hcwk : |Int.sign (P.vert k - q).1 - Int.sign (P.vert (k + 1) - q).1| = 2)
    (hsp : ∃ i, 0 < (P.vert i - q).1) (hsn : ∃ i, (P.vert i - q).1 < 0) :
    angleWeight P q = 0 := by
  have hsum4 := triangle_columnWeight_sum P hn q hsp hsn
  rw [angleWeight_eq_sum,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), Int.sign_eq_neg_one_of_neg hk]
  have step : ∀ i ∈ Finset.univ.erase k,
      (Int.sign (crossZ (P.vert i - q) (P.vert (i + 1) - q)) : ℚ)
        * (|Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1| : ℚ)
      = (|Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1| : ℚ) := fun i hmem => by
    rw [Int.sign_eq_one_of_pos (hi i (Finset.ne_of_mem_erase hmem)), Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl step]
  simp only [← Int.cast_sub, ← Int.cast_abs, ← Int.cast_sum]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hsum4, hcwk]
  push_cast
  norm_num

/-- **Exterior, two-negative case.** On the wrong side of two edges (only edge `c` CCW),
with `cW_c = 2` and an x-straddle, `angleWeight = 0`: `(2·2 − 4)/4 = 0`. -/
lemma angleWeight_eq_zero_of_two_neg (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (c : ZMod P.n)
    (hc : 0 < crossZ (P.vert c - q) (P.vert (c + 1) - q))
    (hi : ∀ j, j ≠ c → crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0)
    (hcwc : |Int.sign (P.vert c - q).1 - Int.sign (P.vert (c + 1) - q).1| = 2)
    (hsp : ∃ i, 0 < (P.vert i - q).1) (hsn : ∃ i, (P.vert i - q).1 < 0) :
    angleWeight P q = 0 := by
  have hsum4 := triangle_columnWeight_sum P hn q hsp hsn
  rw [angleWeight_eq_sum,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c), Int.sign_eq_one_of_pos hc]
  have step : ∀ j ∈ Finset.univ.erase c,
      (Int.sign (crossZ (P.vert j - q) (P.vert (j + 1) - q)) : ℚ)
        * (|Int.sign (P.vert j - q).1 - Int.sign (P.vert (j + 1) - q).1| : ℚ)
      = -(|Int.sign (P.vert j - q).1 - Int.sign (P.vert (j + 1) - q).1| : ℚ) := fun j hmem => by
    rw [Int.sign_eq_neg_one_of_neg (hi j (Finset.ne_of_mem_erase hmem))]; push_cast; ring
  rw [Finset.sum_congr rfl step, Finset.sum_neg_distrib]
  simp only [← Int.cast_sub, ← Int.cast_abs, ← Int.cast_sum]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ c), hsum4, hcwc]
  push_cast
  norm_num

/-- **Exterior, non-straddled.** If all vertices share the same x-side of `q` (constant
`Int.sign (vᵢ−q).1`), every column-weight `|sign diff|` is `0`, so `angleWeight = 0`. This
covers the in-box exterior points whose column is not straddled. -/
lemma angleWeight_eq_zero_of_fst_sign_const (P : LatticePolygon) (q : Pt) (s : ℤ)
    (h : ∀ i, Int.sign (P.vert i - q).1 = s) : angleWeight P q = 0 := by
  rw [angleWeight_eq_sum]
  have hz : ∀ i, (Int.sign (crossZ (P.vert i - q) (P.vert (i + 1) - q)) : ℚ)
      * (|Int.sign (P.vert i - q).1 - Int.sign (P.vert (i + 1) - q).1| : ℚ) = 0 := by
    intro i
    simp only [h i, h (i + 1), sub_self, abs_zero, Int.cast_zero, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const_zero]; simp

/-- A lattice point on edge `k`'s segment is collinear with its endpoints, so the
corner-cross vanishes. This ties `Defs.boundaryLattice` (membership in some `edgeSeg`)
to `crossZ = 0`, the boundary case of the classification. -/
lemma crossZ_eq_zero_of_mem_edgeSeg (P : LatticePolygon) (q : Pt) (k : ZMod P.n)
    (hq : toReal q ∈ P.edgeSeg k) :
    crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0 := by
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hq
  obtain ⟨t, _, hqt⟩ := hq
  have hcross : cross (toReal (P.vert k) - toReal q) (toReal (P.vert (k + 1)) - toReal q) = 0 := by
    rw [← hqt]
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, toReal]
    ring
  have hz : ((crossZ (P.vert k - q) (P.vert (k + 1) - q) : ℤ) : ℝ) = 0 := by
    rw [← hcross]
    simp only [crossZ, cross, toReal, Prod.fst_sub, Prod.snd_sub]
    push_cast
    ring
  exact_mod_cast hz

/-- For a convex combination `q = a•v0 + b•v1` (`a+b=1`), the cross product seen from
`q` to the next edge equals `a` times the corner cross. (Algebraic core of the boundary
classification: on edge `j`, the adjacent edge is seen with sign `a ≥ 0`.) -/
lemma cross_next_eq_smul_corner (v0 v1 v2 q : ℝ × ℝ) (a b : ℝ) (hab : a + b = 1)
    (hq : q = a • v0 + b • v1) :
    cross (v1 - q) (v2 - q) = a * cross (v1 - v0) (v2 - v0) := by
  have hb1 : b = 1 - a := by linarith
  subst hq hb1
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Companion to `cross_next_eq_smul_corner`: the cross product from `q` (on the `v0`–`v1`
segment) to the previous edge equals `b` times the corner cross at `v1`. -/
lemma cross_prev_eq_smul_corner (v0 v1 v2 q : ℝ × ℝ) (a b : ℝ) (hab : a + b = 1)
    (hq : q = a • v0 + b • v1) :
    cross (v0 - q) (v2 - q) = b * cross (v0 - v1) (v2 - v1) := by
  have ha1 : a = 1 - b := by linarith
  subst hq ha1
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `toReal` is injective (`ℤ → ℝ` casts are). Used to read back `t ∈ (0,1)` from
`q ≠` endpoints on an edge segment. -/
lemma toReal_injective : Function.Injective toReal := by
  intro a b h
  simp only [toReal, Prod.mk.injEq] at h
  exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)

/-- Coordinate identities for a convex combination `q = (1−t)•v0 + t•v1`: the x-offsets
from the endpoints are `t` and `(1−t)` multiples of the edge's x-span (opposite signs when
`t ∈ (0,1)` and the edge is non-vertical — the genuine-column-crossing condition). -/
lemma fst_sub_of_combo (v0 v1 q : ℝ × ℝ) (t : ℝ) (hq : q = (1 - t) • v0 + t • v1) :
    (v0 - q).1 = t * (v0.1 - v1.1) ∧ (v1 - q).1 = (1 - t) * (v1.1 - v0.1) := by
  subst hq
  refine ⟨?_, ?_⟩ <;>
    simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul] <;> ring

/-- A vector parallel to two non-parallel vectors is zero (2D). Used for two-zeros: a
point on two distinct edge lines is their shared vertex. -/
lemma eq_zero_of_crossZ_parallel (a b u : Pt) (ha : crossZ a u = 0) (hb : crossZ u b = 0)
    (hab : crossZ a b ≠ 0) : u = 0 := by
  simp only [crossZ] at ha hb hab
  have hu1 : u.1 * (a.1 * b.2 - a.2 * b.1) = 0 := by linear_combination b.1 * ha + a.1 * hb
  have hu2 : u.2 * (a.1 * b.2 - a.2 * b.1) = 0 := by linear_combination b.2 * ha + a.2 * hb
  have h1 : u.1 = 0 := (mul_eq_zero.1 hu1).resolve_right hab
  have h2 : u.2 = 0 := (mul_eq_zero.1 hu2).resolve_right hab
  exact Prod.ext h1 h2

/-- A point on the lines of two adjacent edges (sharing vertex `v1`) is that vertex,
given the corner is non-degenerate. -/
lemma eq_vertex_of_adjacent_crossZ_zero (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) = 0) (h1 : crossZ (v1 - q) (v2 - q) = 0)
    (hnd : crossZ (v0 - v1) (v2 - v1) ≠ 0) : q = v1 := by
  have key : v1 - q = 0 := by
    refine eq_zero_of_crossZ_parallel (v0 - v1) (v2 - v1) (v1 - q) ?_ ?_ hnd
    · have e : crossZ (v0 - v1) (v1 - q) = crossZ (v0 - q) (v1 - q) := by
        simp only [crossZ, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact h0
    · have e : crossZ (v1 - q) (v2 - v1) = crossZ (v1 - q) (v2 - q) := by
        simp only [crossZ, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact h1
  exact (sub_eq_zero.1 key).symm

/-- On an edge's line (`crossZ = 0`), the x-coordinate is determined by the y-coordinate
via the line equation. -/
lemma crossZ_zero_x_eq (q v0 v1 : Pt) (h0 : crossZ (v0 - q) (v1 - q) = 0) :
    q.1 * (v1.2 - v0.2) = (v1.2 - q.2) * v0.1 + (q.2 - v0.2) * v1.1 := by
  simp only [crossZ, Prod.fst_sub, Prod.snd_sub] at h0
  linear_combination -h0

/-- Converse direction: a convex combination of edge `k`'s endpoints lies on its
segment. (With `crossZ_k = 0` and the other crosses positive, the barycentric weights
are nonnegative, placing `q` on the segment — hence on the boundary.) -/
lemma mem_edgeSeg_of_convex (P : LatticePolygon) (q : Pt) (k : ZMod P.n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hq : toReal q = a • toReal (P.vert k) + b • toReal (P.vert (k + 1))) :
    toReal q ∈ P.edgeSeg k :=
  ⟨a, b, ha, hb, hab, hq.symm⟩

/-- A point seeing every edge strictly off its line (`all crossZ ≠ 0`) is off the
boundary. So interior lattice points (`winding = 1`, off-boundary) have `all crossZ ≠ 0`. -/
lemma not_mem_boundary_of_crossZ_ne (P : LatticePolygon) (q : Pt)
    (hne : ∀ k, crossZ (P.vert k - q) (P.vert (k + 1) - q) ≠ 0) :
    toReal q ∉ P.boundary := by
  rw [LatticePolygon.boundary, Set.mem_iUnion]
  push_neg
  intro k hmem
  exact hne k (crossZ_eq_zero_of_mem_edgeSeg P q k hmem)

/-- **Corner-cross = half-plane test.** `crossZ(vⱼ−q, vⱼ₊₁−q) = crossZ(vⱼ₊₁−vⱼ, q−vⱼ)`,
the signed area of the directed edge `j` against `q`. So `crossZ_j > 0` ⟺ `q` lies
strictly left of directed edge `j`; `= 0` ⟺ `q` is on edge `j`'s line; `< 0` ⟺ right.
This is the bridge from the per-point `crossZ` hypotheses to `q`'s geometric position. -/
lemma corner_cross_eq_edge_cross (P : LatticePolygon) (q : Pt) (j : ZMod P.n) :
    crossZ (P.vert j - q) (P.vert (j + 1) - q)
      = crossZ (P.vert (j + 1) - P.vert j) (q - P.vert j) := by
  simp only [crossZ, Prod.fst_sub, Prod.snd_sub]; ring

/-- The real `cross` used inside `edgeWind` for edge `j` equals the integer corner-cross
`crossZ(vⱼ−q, vⱼ₊₁−q)`. Hence `winding`'s sign test for each edge is exactly the
half-plane test, tying `Defs.winding` to the per-point `crossZ` analysis. -/
lemma cross_edge_eq_crossZ (P : LatticePolygon) (q : Pt) (j : ZMod P.n) :
    cross (toReal (P.vert (j + 1)) - toReal (P.vert j)) (toReal q - toReal (P.vert j))
      = (crossZ (P.vert j - q) (P.vert (j + 1) - q) : ℝ) := by
  simp only [cross, crossZ, toReal, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-- `edgeWind` for edge `j` at a lattice point, rewritten with integer `y`-brackets and
the integer corner-cross sign. The winding number is the sum of these over all edges,
so it is fully determined by the per-edge `crossZ` signs and vertical spans. -/
lemma edgeWind_toReal_eq (P : LatticePolygon) (q : Pt) (j : ZMod P.n) :
    edgeWind (toReal (P.vert j)) (toReal (P.vert (j + 1))) (toReal q)
      = if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
            ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then 1
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
            ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1
        else 0 := by
  unfold LatticePolygon.edgeWind
  rw [cross_edge_eq_crossZ]
  simp only [toReal, Int.cast_le, Int.cast_lt, Int.cast_pos, Int.cast_lt_zero]

/-- The winding number at a lattice point as a `crossZ`-based integer sum: each edge
contributes `+1`/`−1`/`0` by its vertical bracket and corner-cross sign. -/
lemma winding_toReal_eq (P : LatticePolygon) (q : Pt) :
    P.winding (toReal q)
      = ∑ j, (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
            ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
            ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1
        else 0) := by
  unfold LatticePolygon.winding
  exact Finset.sum_congr rfl (fun j _ => edgeWind_toReal_eq P q j)

/-- When `q` sees every edge CCW (all `crossZ > 0`), the `−1` branch never fires and the
winding is just the number of upward edges whose vertical bracket contains `q.2`. -/
lemma winding_of_crossZ_pos (P : LatticePolygon) (q : Pt)
    (h : ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) :
    P.winding (toReal q)
      = ∑ j, (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0) := by
  rw [winding_toReal_eq]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpos := h j
  have hc : ¬ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 := not_lt.mpr hpos.le
  simp only [hpos, hc, and_true, and_false, if_false]

/-- **Crossings balance.** Around the closed polygon, the number of upward edges whose
half-open bracket contains `q.2` equals the number of downward ones — the net signed
crossing of a horizontal line is `0`. (Each term telescopes to `g(vⱼ) − g(vⱼ₊₁)` where
`g v = [v.2 ≤ q.2]`.) -/
lemma sum_upward_eq_downward (P : LatticePolygon) (q : Pt) :
    (∑ j, (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0))
      = ∑ j, (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0) := by
  have key : ∀ j : ZMod P.n,
      (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0)
        - (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0)
      = (if (P.vert j).2 ≤ q.2 then (1 : ℤ) else 0)
        - (if (P.vert (j + 1)).2 ≤ q.2 then (1 : ℤ) else 0) := fun j => by
    split_ifs <;> omega
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun j _ => key j),
    Finset.sum_sub_distrib, sub_eq_zero]
  exact (Fintype.sum_equiv (Equiv.addRight 1)
    (fun j => if (P.vert (j + 1)).2 ≤ q.2 then (1 : ℤ) else 0)
    (fun j => if (P.vert j).2 ≤ q.2 then (1 : ℤ) else 0) (fun _ => rfl)).symm

/-- **Total crossings = 2.** For a triangle whose vertices straddle the horizontal line
`y = q.2` (some vertex weakly below, some strictly above), the line crosses exactly two
edges (counting both directions). Each edge's crossing indicator is `|I(vⱼ) − I(vⱼ₊₁)|`
with `I v = [v.2 ≤ q.2]`, and the cyclic sum is `2`. -/
lemma sum_crossing_eq_two (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    (∑ j, ((if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0)
      + (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0))) = 2 := by
  have hterm : ∀ j : ZMod P.n,
      (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0)
        + (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0)
      = |(if (P.vert j).2 ≤ q.2 then (1 : ℤ) else 0)
          - (if (P.vert (j + 1)).2 ≤ q.2 then (1 : ℤ) else 0)| := fun j => by
    split_ifs <;> simp_all <;> omega
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  obtain ⟨e1, e2, e3, _, _, _⟩ := zmodPn_idx P hn
  obtain ⟨jlo, hjlo⟩ := hlo
  obtain ⟨jhi, hjhi⟩ := hhi
  have ho : (if (P.vert 0).2 ≤ q.2 then (1 : ℤ) else 0) = 1
      ∨ (if (P.vert 1).2 ≤ q.2 then (1 : ℤ) else 0) = 1
      ∨ (if (P.vert 2).2 ≤ q.2 then (1 : ℤ) else 0) = 1 := by
    rcases zmodPn_cases P hn jlo with h | h | h <;> subst h
    · exact Or.inl (if_pos hjlo)
    · exact Or.inr (Or.inl (if_pos hjlo))
    · exact Or.inr (Or.inr (if_pos hjlo))
  have hz : (if (P.vert 0).2 ≤ q.2 then (1 : ℤ) else 0) = 0
      ∨ (if (P.vert 1).2 ≤ q.2 then (1 : ℤ) else 0) = 0
      ∨ (if (P.vert 2).2 ≤ q.2 then (1 : ℤ) else 0) = 0 := by
    rcases zmodPn_cases P hn jhi with h | h | h <;> subst h
    · exact Or.inl (if_neg (not_le.mpr hjhi))
    · exact Or.inr (Or.inl (if_neg (not_le.mpr hjhi)))
    · exact Or.inr (Or.inr (if_neg (not_le.mpr hjhi)))
  rw [sum_zmodPn P hn (fun j => |(if (P.vert j).2 ≤ q.2 then (1 : ℤ) else 0)
      - (if (P.vert (j + 1)).2 ≤ q.2 then (1 : ℤ) else 0)|), e1, e2, e3]
  exact indicator_diff_abs_sum _ _ _ (by split_ifs <;> simp) (by split_ifs <;> simp)
    (by split_ifs <;> simp) hz ho

/-- The total downward crossings of a straddling horizontal line is `1`. -/
lemma down_sum_eq_one (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    (∑ j, (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0)) = 1 := by
  have htot := sum_crossing_eq_two P hn q hlo hhi
  have hbal := sum_upward_eq_downward P q
  rw [Finset.sum_add_distrib, hbal] at htot
  omega

/-- **Winding = 1 at an interior point (triangle).** If `q` sees every edge CCW (all
`crossZ > 0`) and its column-height is straddled vertically (some vertex weakly below,
some strictly above `q.2`), then `winding q = 1`: winding equals the upward crossings,
which equal the downward ones, and they total `2`, so each is `1`. -/
lemma winding_eq_one_of_crossZ_pos (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (h : ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q))
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    P.winding (toReal q) = 1 := by
  rw [winding_of_crossZ_pos P q h]
  have htot := sum_crossing_eq_two P hn q hlo hhi
  have hbal := sum_upward_eq_downward P q
  rw [Finset.sum_add_distrib, ← hbal] at htot
  omega

/-- For a point on the wrong side of exactly edge `k` (`crossZ_k < 0`, others `> 0`),
the winding splits as the upward crossings of the CCW edges minus the downward crossing
of edge `k`. -/
lemma winding_of_one_crossZ_neg (P : LatticePolygon) (q : Pt) (k : ZMod P.n)
    (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0)
    (hi : ∀ j, j ≠ k → 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) :
    P.winding (toReal q)
      = (∑ j ∈ Finset.univ.erase k,
          (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0))
        - (if (P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert k).2 then (1 : ℤ) else 0) := by
  rw [winding_toReal_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hck : ¬ (0 < crossZ (P.vert k - q) (P.vert (k + 1) - q)) := not_lt.mpr hk.le
  rw [show (if (P.vert k).2 ≤ q.2 ∧ q.2 < (P.vert (k + 1)).2
          ∧ 0 < crossZ (P.vert k - q) (P.vert (k + 1) - q) then (1 : ℤ)
        else if (P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert k).2
          ∧ crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0 then -1 else 0)
      = -(if (P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert k).2 then (1 : ℤ) else 0) from by
        simp only [hck, hk, and_true, and_false, if_false]; split_ifs <;> rfl]
  rw [Finset.sum_congr rfl (fun j hj => by
    have hpos := hi j (Finset.ne_of_mem_erase hj)
    have hc : ¬ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 := not_lt.mpr hpos.le
    simp only [hpos, hc, and_true, and_false, if_false]
      : ∀ j ∈ Finset.univ.erase k,
        (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
            ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
          else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
            ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0)
        = (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0))]
  ring

/-- Two-negative case: on the wrong side of all but edge `c`, the winding is the upward
crossing of edge `c` minus the downward crossings of the two wrong-side edges. -/
lemma winding_of_two_crossZ_neg (P : LatticePolygon) (q : Pt) (c : ZMod P.n)
    (hc : 0 < crossZ (P.vert c - q) (P.vert (c + 1) - q))
    (hi : ∀ j, j ≠ c → crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0) :
    P.winding (toReal q)
      = (if (P.vert c).2 ≤ q.2 ∧ q.2 < (P.vert (c + 1)).2 then (1 : ℤ) else 0)
        - ∑ j ∈ Finset.univ.erase c,
          (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0) := by
  rw [winding_toReal_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ c)]
  have hcc : ¬ (crossZ (P.vert c - q) (P.vert (c + 1) - q) < 0) := not_lt.mpr hc.le
  rw [show (if (P.vert c).2 ≤ q.2 ∧ q.2 < (P.vert (c + 1)).2
          ∧ 0 < crossZ (P.vert c - q) (P.vert (c + 1) - q) then (1 : ℤ)
        else if (P.vert (c + 1)).2 ≤ q.2 ∧ q.2 < (P.vert c).2
          ∧ crossZ (P.vert c - q) (P.vert (c + 1) - q) < 0 then -1 else 0)
      = (if (P.vert c).2 ≤ q.2 ∧ q.2 < (P.vert (c + 1)).2 then (1 : ℤ) else 0) from by
        simp only [hc, hcc, and_true, and_false, if_false]]
  rw [Finset.sum_congr rfl (fun j hj => by
    have hneg := hi j (Finset.ne_of_mem_erase hj)
    have hcnp : ¬ (0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) := not_lt.mpr hneg.le
    simp only [hneg, hcnp, and_true, and_false, if_false]; split_ifs <;> rfl
      : ∀ j ∈ Finset.univ.erase c,
        (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
            ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
          else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
            ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0)
        = -(if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0))]
  rw [Finset.sum_neg_distrib]
  ring

/-- For a point on the wrong side of exactly edge `k`, with a vertically straddled
column, `winding = 1 − (edge-k crossing indicator) ∈ {0, 1}`: it is `0` exactly when
edge `k` brackets `q.2` (the geometric exterior condition). -/
lemma winding_one_neg_eq (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0)
    (hi : ∀ j, j ≠ k → 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q))
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    P.winding (toReal q)
      = 1 - ((if (P.vert k).2 ≤ q.2 ∧ q.2 < (P.vert (k + 1)).2 then (1 : ℤ) else 0)
        + (if (P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert k).2 then (1 : ℤ) else 0)) := by
  rw [winding_of_one_crossZ_neg P q k hk hi]
  have hup : (∑ j, (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0)) = 1 := by
    have htot := sum_crossing_eq_two P hn q hlo hhi
    have hbal := sum_upward_eq_downward P q
    rw [Finset.sum_add_distrib, ← hbal] at htot
    omega
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hup]
  ring

/-- **Barycentric identity (x-coordinate).** `q.1` weighted by the total corner-cross
equals the corner-crosses (sub-triangle areas) weighting the vertices' x-coordinates.
With all `crossZ > 0` and total `> 0`, `q.1` is a strict convex combination of the
`vᵢ.1`, hence strictly between their min and max — the x-straddle. -/
lemma barycentric_x (q : Pt) (v0 v1 v2 : Pt) :
    q.1 * (crossZ (v0 - q) (v1 - q) + crossZ (v1 - q) (v2 - q) + crossZ (v2 - q) (v0 - q))
      = crossZ (v1 - q) (v2 - q) * v0.1 + crossZ (v2 - q) (v0 - q) * v1.1
        + crossZ (v0 - q) (v1 - q) * v2.1 := by
  simp only [crossZ, Prod.fst_sub, Prod.snd_sub]; ring

/-- A positive cross-multiplication preserves sign: `x·a = b·y` with `a,b > 0` ⟹
`sign x = sign y`. -/
lemma sign_eq_of_mul_eq_mul {x y a b : ℤ} (ha : 0 < a) (hb : 0 < b) (h : x * a = b * y) :
    Int.sign x = Int.sign y := by
  have h2 := congrArg Int.sign h
  simp only [Int.sign_mul, Int.sign_eq_one_of_pos ha, Int.sign_eq_one_of_pos hb,
    mul_one, one_mul] at h2
  exact h2

/-- The sign of a positive combination lies between the signs of its parts: if
`Z·D = A·X + B·Y` with `D,A,B > 0`, then `sign Z` is between `sign X` and `sign Y`
(stated as the column-weight betweenness equation). -/
lemma sign_between_of_pos_combo (X Y Z D A B : ℤ) (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (h : Z * D = A * X + B * Y) :
    |Int.sign Y - Int.sign Z| + |Int.sign Z - Int.sign X| = |Int.sign X - Int.sign Y| := by
  have hZ : Int.sign Z = Int.sign (A * X + B * Y) := by
    rw [← h, Int.sign_mul, Int.sign_eq_one_of_pos hD, mul_one]
  rw [hZ]
  rcases lt_trichotomy X 0 with hX | hX | hX <;>
    rcases lt_trichotomy Y 0 with hY | hY | hY <;>
    rcases lt_trichotomy (A * X + B * Y) 0 with hW | hW | hW <;>
    first
      | (exfalso; nlinarith)
      | simp_all [Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos]

/-- **Offset barycentric identity (x).** The cross-weighted x-offsets from `q` sum to `0`
— the natural form for the exterior sign analysis. -/
lemma barycentric_offset_x (q v0 v1 v2 : Pt) :
    crossZ (v1 - q) (v2 - q) * (v0 - q).1 + crossZ (v2 - q) (v0 - q) * (v1 - q).1
      + crossZ (v0 - q) (v1 - q) * (v2 - q).1 = 0 := by
  simp only [Prod.fst_sub]
  linear_combination -barycentric_x q v0 v1 v2

/-- **Betweenness for the one-negative exterior case.** When edge `k` is wrong-side and the
others CCW, the third vertex's x-sign lies between edge `k`'s endpoints' — because
`(v_{k+2}−q).1·(−crossZ_k)` is a positive combination of the endpoint x-offsets. -/
lemma hbtw_of_neg_edge (q v0 v1 v2 : Pt)
    (hk : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) :
    |Int.sign (v1 - q).1 - Int.sign (v2 - q).1| + |Int.sign (v2 - q).1 - Int.sign (v0 - q).1|
      = |Int.sign (v0 - q).1 - Int.sign (v1 - q).1| := by
  have hoff := barycentric_offset_x q v0 v1 v2
  refine sign_between_of_pos_combo (v0 - q).1 (v1 - q).1 (v2 - q).1
    (-crossZ (v0 - q) (v1 - q)) (crossZ (v1 - q) (v2 - q)) (crossZ (v2 - q) (v0 - q))
    (by linarith) h1 h2 ?_
  linear_combination -hoff

/-- Betweenness for the two-negative exterior case (edge `v0v1` the lone CCW edge): the
third vertex's x-sign lies between, via the same positive-combination argument. -/
lemma hbtw_of_pos_edge (q v0 v1 v2 : Pt)
    (hk : 0 < crossZ (v0 - q) (v1 - q)) (h1 : crossZ (v1 - q) (v2 - q) < 0)
    (h2 : crossZ (v2 - q) (v0 - q) < 0) :
    |Int.sign (v1 - q).1 - Int.sign (v2 - q).1| + |Int.sign (v2 - q).1 - Int.sign (v0 - q).1|
      = |Int.sign (v0 - q).1 - Int.sign (v1 - q).1| := by
  have hoff := barycentric_offset_x q v0 v1 v2
  refine sign_between_of_pos_combo (v0 - q).1 (v1 - q).1 (v2 - q).1
    (crossZ (v0 - q) (v1 - q)) (-crossZ (v1 - q) (v2 - q)) (-crossZ (v2 - q) (v0 - q))
    hk (by linarith) (by linarith) ?_
  linear_combination hoff

/-- **Barycentric identity (y-coordinate).** -/
lemma barycentric_y (q : Pt) (v0 v1 v2 : Pt) :
    q.2 * (crossZ (v0 - q) (v1 - q) + crossZ (v1 - q) (v2 - q) + crossZ (v2 - q) (v0 - q))
      = crossZ (v1 - q) (v2 - q) * v0.2 + crossZ (v2 - q) (v0 - q) * v1.2
        + crossZ (v0 - q) (v1 - q) * v2.2 := by
  simp only [crossZ, Prod.fst_sub, Prod.snd_sub]; ring

/-- If `q` is on edge `v0v1`'s line (`crossZ = 0`) and on the correct side of the other
two edges, its barycentric weights on `v0, v1` are nonnegative and sum to `1`: `q` is a
convex combination of `v0, v1`, hence on the segment. -/
lemma convex_combo_of_crossZ_zero (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) = 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ toReal q = a • toReal v0 + b • toReal v1 := by
  set c1 : ℤ := crossZ (v1 - q) (v2 - q) with hc1
  set c2 : ℤ := crossZ (v2 - q) (v0 - q) with hc2
  have hx : q.1 * (c1 + c2) = c1 * v0.1 + c2 * v1.1 := by
    have hb := barycentric_x q v0 v1 v2; rw [h0] at hb
    simp only [zero_add, zero_mul, add_zero] at hb; linear_combination hb
  have hy : q.2 * (c1 + c2) = c1 * v0.2 + c2 * v1.2 := by
    have hb := barycentric_y q v0 v1 v2; rw [h0] at hb
    simp only [zero_add, zero_mul, add_zero] at hb; linear_combination hb
  have hTR : (0 : ℝ) < (c1 : ℝ) + (c2 : ℝ) := by
    have : (0 : ℤ) < c1 + c2 := by linarith
    exact_mod_cast this
  have hxR : (q.1 : ℝ) * ((c1 : ℝ) + c2) = (c1 : ℝ) * v0.1 + (c2 : ℝ) * v1.1 := by exact_mod_cast hx
  have hyR : (q.2 : ℝ) * ((c1 : ℝ) + c2) = (c1 : ℝ) * v0.2 + (c2 : ℝ) * v1.2 := by exact_mod_cast hy
  refine ⟨(c1 : ℝ) / ((c1 : ℝ) + c2), (c2 : ℝ) / ((c1 : ℝ) + c2),
    div_nonneg (by exact_mod_cast h1.le) hTR.le, div_nonneg (by exact_mod_cast h2.le) hTR.le,
    by field_simp, ?_⟩
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, Prod.smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul]
    show (q.1 : ℝ) = (c1 : ℝ) / ((c1 : ℝ) + c2) * (v0.1 : ℝ)
      + (c2 : ℝ) / ((c1 : ℝ) + c2) * (v1.1 : ℝ)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hTR.ne']
    linear_combination hxR
  · rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul]
    show (q.2 : ℝ) = (c1 : ℝ) / ((c1 : ℝ) + c2) * (v0.2 : ℝ)
      + (c2 : ℝ) / ((c1 : ℝ) + c2) * (v1.2 : ℝ)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hTR.ne']
    linear_combination hyR

/-- A lattice point on edge `k`'s line and on the correct side of the other two edges
lies on edge `k`'s segment — hence on the boundary. -/
lemma mem_edgeSeg_of_crossZ_zero (P : LatticePolygon) (q : Pt) (k : ZMod P.n)
    (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : 0 < crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
    (h2 : 0 < crossZ (P.vert (k + 2) - q) (P.vert k - q)) :
    toReal q ∈ P.edgeSeg k := by
  obtain ⟨a, b, ha, hb, hab, hq⟩ :=
    convex_combo_of_crossZ_zero q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2)) h0 h1 h2
  exact mem_edgeSeg_of_convex P q k a b ha hb hab hq

/-- A lattice point on edge `k`'s line whose height is bracketed by the endpoints lies on
edge `k`'s segment (the weights come from the y-coordinate; x follows from the line
equation). -/
lemma mem_edgeSeg_of_bracket (P : LatticePolygon) (q : Pt) (k : ZMod P.n)
    (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (hlt : (P.vert k).2 ≤ q.2) (hgt : q.2 < (P.vert (k + 1)).2) :
    toReal q ∈ P.edgeSeg k := by
  have hdy : (0 : ℝ) < ((P.vert (k + 1)).2 : ℝ) - ((P.vert k).2 : ℝ) := by
    have h1 : ((P.vert k).2 : ℝ) ≤ q.2 := by exact_mod_cast hlt
    have h2 : (q.2 : ℝ) < ((P.vert (k + 1)).2 : ℝ) := by exact_mod_cast hgt
    linarith
  have hxR : (q.1 : ℝ) * (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2)
      = (((P.vert (k + 1)).2 : ℝ) - q.2) * (P.vert k).1
        + ((q.2 : ℝ) - (P.vert k).2) * (P.vert (k + 1)).1 := by
    exact_mod_cast crossZ_zero_x_eq q (P.vert k) (P.vert (k + 1)) h0
  refine mem_edgeSeg_of_convex P q k
    ((((P.vert (k + 1)).2 : ℝ) - q.2) / (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2))
    (((q.2 : ℝ) - (P.vert k).2) / (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2)) ?_ ?_ ?_ ?_
  · refine div_nonneg ?_ hdy.le
    have : (q.2 : ℝ) < ((P.vert (k + 1)).2 : ℝ) := by exact_mod_cast hgt
    linarith
  · refine div_nonneg ?_ hdy.le
    have : ((P.vert k).2 : ℝ) ≤ q.2 := by exact_mod_cast hlt
    linarith
  · field_simp
    ring
  · refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul]
      show (q.1 : ℝ) = (((P.vert (k + 1)).2 : ℝ) - q.2) / (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2)
          * ((P.vert k).1 : ℝ)
        + ((q.2 : ℝ) - (P.vert k).2) / (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2)
          * ((P.vert (k + 1)).1 : ℝ)
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hdy.ne']
      linear_combination hxR
    · rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul]
      show (q.2 : ℝ) = (((P.vert (k + 1)).2 : ℝ) - q.2) / (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2)
          * ((P.vert k).2 : ℝ)
        + ((q.2 : ℝ) - (P.vert k).2) / (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2)
          * ((P.vert (k + 1)).2 : ℝ)
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hdy.ne']
      ring

/-- Reverse-bracket version of `mem_edgeSeg_of_bracket` (endpoints in the other order). -/
lemma mem_edgeSeg_of_bracket' (P : LatticePolygon) (q : Pt) (k : ZMod P.n)
    (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (hlt : (P.vert (k + 1)).2 ≤ q.2) (hgt : q.2 < (P.vert k).2) :
    toReal q ∈ P.edgeSeg k := by
  have hdy : (0 : ℝ) < ((P.vert k).2 : ℝ) - ((P.vert (k + 1)).2 : ℝ) := by
    have h1 : ((P.vert (k + 1)).2 : ℝ) ≤ q.2 := by exact_mod_cast hlt
    have h2 : (q.2 : ℝ) < ((P.vert k).2 : ℝ) := by exact_mod_cast hgt
    linarith
  have hxR : (q.1 : ℝ) * (((P.vert k).2 : ℝ) - (P.vert (k + 1)).2)
      = ((q.2 : ℝ) - (P.vert (k + 1)).2) * (P.vert k).1
        + (((P.vert k).2 : ℝ) - q.2) * (P.vert (k + 1)).1 := by
    have hC : (q.1 : ℝ) * (((P.vert (k + 1)).2 : ℝ) - (P.vert k).2)
        = (((P.vert (k + 1)).2 : ℝ) - q.2) * (P.vert k).1
          + ((q.2 : ℝ) - (P.vert k).2) * (P.vert (k + 1)).1 := by
      exact_mod_cast crossZ_zero_x_eq q (P.vert k) (P.vert (k + 1)) h0
    linear_combination -hC
  refine mem_edgeSeg_of_convex P q k
    (((q.2 : ℝ) - (P.vert (k + 1)).2) / (((P.vert k).2 : ℝ) - (P.vert (k + 1)).2))
    ((((P.vert k).2 : ℝ) - q.2) / (((P.vert k).2 : ℝ) - (P.vert (k + 1)).2)) ?_ ?_ ?_ ?_
  · refine div_nonneg ?_ hdy.le
    have : ((P.vert (k + 1)).2 : ℝ) ≤ q.2 := by exact_mod_cast hlt
    linarith
  · refine div_nonneg ?_ hdy.le
    have : (q.2 : ℝ) < ((P.vert k).2 : ℝ) := by exact_mod_cast hgt
    linarith
  · field_simp
    ring
  · refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul]
      show (q.1 : ℝ) = ((q.2 : ℝ) - (P.vert (k + 1)).2) / (((P.vert k).2 : ℝ) - (P.vert (k + 1)).2)
          * ((P.vert k).1 : ℝ)
        + (((P.vert k).2 : ℝ) - q.2) / (((P.vert k).2 : ℝ) - (P.vert (k + 1)).2)
          * ((P.vert (k + 1)).1 : ℝ)
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hdy.ne']
      linear_combination hxR
    · rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul]
      show (q.2 : ℝ) = ((q.2 : ℝ) - (P.vert (k + 1)).2) / (((P.vert k).2 : ℝ) - (P.vert (k + 1)).2)
          * ((P.vert k).2 : ℝ)
        + (((P.vert k).2 : ℝ) - q.2) / (((P.vert k).2 : ℝ) - (P.vert (k + 1)).2)
          * ((P.vert (k + 1)).2 : ℝ)
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hdy.ne']
      ring

/-- An off-boundary point on edge `k`'s line with the other two edges CCW is impossible:
it would lie on edge `k`'s segment. (The main case of `crossZ = 0` ruling out interior
lattice points.) -/
lemma not_crossZ_zero_others_pos (P : LatticePolygon) (q : Pt) (k : ZMod P.n)
    (hbdry : toReal q ∉ P.boundary)
    (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : 0 < crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
    (h2 : 0 < crossZ (P.vert (k + 2) - q) (P.vert k - q)) : False :=
  hbdry (Set.mem_iUnion.2 ⟨k, mem_edgeSeg_of_crossZ_zero P q k h0 h1 h2⟩)

/-- A point seeing all three edges CCW has some vertex strictly to its right (its
x-coordinate is a strict convex combination of the vertices'). -/
lemma exists_vertex_right (q v0 v1 v2 : Pt)
    (h0 : 0 < crossZ (v0 - q) (v1 - q)) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) :
    q.1 < v0.1 ∨ q.1 < v1.1 ∨ q.1 < v2.1 := by
  by_contra h
  push_neg at h
  obtain ⟨hv0, hv1, hv2⟩ := h
  have key : crossZ (v1 - q) (v2 - q) * (q.1 - v0.1) + crossZ (v2 - q) (v0 - q) * (q.1 - v1.1)
      + crossZ (v0 - q) (v1 - q) * (q.1 - v2.1) = 0 := by
    linear_combination barycentric_x q v0 v1 v2
  have t0 := mul_nonneg h1.le (sub_nonneg.2 hv0)
  have t1 := mul_nonneg h2.le (sub_nonneg.2 hv1)
  have t2 := mul_nonneg h0.le (sub_nonneg.2 hv2)
  have z0 : crossZ (v1 - q) (v2 - q) * (q.1 - v0.1) = 0 := by linarith
  have z1 : crossZ (v2 - q) (v0 - q) * (q.1 - v1.1) = 0 := by linarith
  have e0 : q.1 - v0.1 = 0 := (mul_eq_zero.1 z0).resolve_left (by linarith)
  have e1 : q.1 - v1.1 = 0 := (mul_eq_zero.1 z1).resolve_left (by linarith)
  have hc0 : crossZ (v0 - q) (v1 - q) = 0 := by
    simp only [crossZ, Prod.fst_sub, Prod.snd_sub]
    rw [show v0.1 - q.1 = 0 by linarith, show v1.1 - q.1 = 0 by linarith]; ring
  linarith

/-- A point seeing all three edges CCW has some vertex strictly to its left. -/
lemma exists_vertex_left (q v0 v1 v2 : Pt)
    (h0 : 0 < crossZ (v0 - q) (v1 - q)) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) :
    v0.1 < q.1 ∨ v1.1 < q.1 ∨ v2.1 < q.1 := by
  by_contra h
  push_neg at h
  obtain ⟨hv0, hv1, hv2⟩ := h
  have key : crossZ (v1 - q) (v2 - q) * (v0.1 - q.1) + crossZ (v2 - q) (v0 - q) * (v1.1 - q.1)
      + crossZ (v0 - q) (v1 - q) * (v2.1 - q.1) = 0 := by
    linear_combination -barycentric_x q v0 v1 v2
  have t0 := mul_nonneg h1.le (sub_nonneg.2 hv0)
  have t1 := mul_nonneg h2.le (sub_nonneg.2 hv1)
  have t2 := mul_nonneg h0.le (sub_nonneg.2 hv2)
  have z0 : crossZ (v1 - q) (v2 - q) * (v0.1 - q.1) = 0 := by linarith
  have z1 : crossZ (v2 - q) (v0 - q) * (v1.1 - q.1) = 0 := by linarith
  have e0 : v0.1 - q.1 = 0 := (mul_eq_zero.1 z0).resolve_left (by linarith)
  have e1 : v1.1 - q.1 = 0 := (mul_eq_zero.1 z1).resolve_left (by linarith)
  have hc0 : crossZ (v0 - q) (v1 - q) = 0 := by
    simp only [crossZ, Prod.fst_sub, Prod.snd_sub]
    rw [show v0.1 - q.1 = 0 by linarith, show v1.1 - q.1 = 0 by linarith]; ring
  linarith

/-- **Interior, clean interface.** For a triangle, `all crossZ > 0` alone gives
`angleWeight = 1` — the x-straddle is automatic from `exists_vertex_left/right`. -/
lemma angleWeight_eq_one_of_crossZ_pos (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (h : ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) :
    angleWeight P q = 1 := by
  obtain ⟨e1, e2, e3, _, _, _⟩ := zmodPn_idx P hn
  have h0 := h 0; rw [e1] at h0
  have h1 := h 1; rw [e2] at h1
  have h2 := h 2; rw [e3] at h2
  refine angleWeight_interior_triangle P hn q h ?_ ?_
  · rcases exists_vertex_right q (P.vert 0) (P.vert 1) (P.vert 2) h0 h1 h2 with hr | hr | hr
    · exact ⟨0, by rw [Prod.fst_sub]; linarith⟩
    · exact ⟨1, by rw [Prod.fst_sub]; linarith⟩
    · exact ⟨2, by rw [Prod.fst_sub]; linarith⟩
  · rcases exists_vertex_left q (P.vert 0) (P.vert 1) (P.vert 2) h0 h1 h2 with hl | hl | hl
    · exact ⟨0, by rw [Prod.fst_sub]; linarith⟩
    · exact ⟨1, by rw [Prod.fst_sub]; linarith⟩
    · exact ⟨2, by rw [Prod.fst_sub]; linarith⟩

/-- A point seeing all three edges CCW has some vertex strictly above it. -/
lemma exists_vertex_above (q v0 v1 v2 : Pt)
    (h0 : 0 < crossZ (v0 - q) (v1 - q)) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) :
    q.2 < v0.2 ∨ q.2 < v1.2 ∨ q.2 < v2.2 := by
  by_contra h
  push_neg at h
  obtain ⟨hv0, hv1, hv2⟩ := h
  have key : crossZ (v1 - q) (v2 - q) * (q.2 - v0.2) + crossZ (v2 - q) (v0 - q) * (q.2 - v1.2)
      + crossZ (v0 - q) (v1 - q) * (q.2 - v2.2) = 0 := by
    linear_combination barycentric_y q v0 v1 v2
  have t0 := mul_nonneg h1.le (sub_nonneg.2 hv0)
  have t1 := mul_nonneg h2.le (sub_nonneg.2 hv1)
  have t2 := mul_nonneg h0.le (sub_nonneg.2 hv2)
  have z0 : crossZ (v1 - q) (v2 - q) * (q.2 - v0.2) = 0 := by linarith
  have z1 : crossZ (v2 - q) (v0 - q) * (q.2 - v1.2) = 0 := by linarith
  have e0 : q.2 - v0.2 = 0 := (mul_eq_zero.1 z0).resolve_left (by linarith)
  have e1 : q.2 - v1.2 = 0 := (mul_eq_zero.1 z1).resolve_left (by linarith)
  have hc0 : crossZ (v0 - q) (v1 - q) = 0 := by
    simp only [crossZ, Prod.fst_sub, Prod.snd_sub]
    rw [show v0.2 - q.2 = 0 by linarith, show v1.2 - q.2 = 0 by linarith]; ring
  linarith

/-- A point seeing all three edges CCW has some vertex strictly below it. -/
lemma exists_vertex_below (q v0 v1 v2 : Pt)
    (h0 : 0 < crossZ (v0 - q) (v1 - q)) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) :
    v0.2 < q.2 ∨ v1.2 < q.2 ∨ v2.2 < q.2 := by
  by_contra h
  push_neg at h
  obtain ⟨hv0, hv1, hv2⟩ := h
  have key : crossZ (v1 - q) (v2 - q) * (v0.2 - q.2) + crossZ (v2 - q) (v0 - q) * (v1.2 - q.2)
      + crossZ (v0 - q) (v1 - q) * (v2.2 - q.2) = 0 := by
    linear_combination -barycentric_y q v0 v1 v2
  have t0 := mul_nonneg h1.le (sub_nonneg.2 hv0)
  have t1 := mul_nonneg h2.le (sub_nonneg.2 hv1)
  have t2 := mul_nonneg h0.le (sub_nonneg.2 hv2)
  have z0 : crossZ (v1 - q) (v2 - q) * (v0.2 - q.2) = 0 := by linarith
  have z1 : crossZ (v2 - q) (v0 - q) * (v1.2 - q.2) = 0 := by linarith
  have e0 : v0.2 - q.2 = 0 := (mul_eq_zero.1 z0).resolve_left (by linarith)
  have e1 : v1.2 - q.2 = 0 := (mul_eq_zero.1 z1).resolve_left (by linarith)
  have hc0 : crossZ (v0 - q) (v1 - q) = 0 := by
    simp only [crossZ, Prod.fst_sub, Prod.snd_sub]
    rw [show v0.2 - q.2 = 0 by linarith, show v1.2 - q.2 = 0 by linarith]; ring
  linarith

/-- **Winding = 1, clean interface.** For a triangle, `all crossZ > 0` alone gives
`winding = 1` — the y-straddle is automatic from `exists_vertex_above/below`. -/
lemma winding_eq_one_of_crossZ_pos' (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (h : ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) :
    P.winding (toReal q) = 1 := by
  obtain ⟨e1, e2, e3, _, _, _⟩ := zmodPn_idx P hn
  have h0 := h 0; rw [e1] at h0
  have h1 := h 1; rw [e2] at h1
  have h2 := h 2; rw [e3] at h2
  refine winding_eq_one_of_crossZ_pos P hn q h ?_ ?_
  · rcases exists_vertex_below q (P.vert 0) (P.vert 1) (P.vert 2) h0 h1 h2 with hb | hb | hb
    · exact ⟨0, hb.le⟩
    · exact ⟨1, hb.le⟩
    · exact ⟨2, hb.le⟩
  · rcases exists_vertex_above q (P.vert 0) (P.vert 1) (P.vert 2) h0 h1 h2 with ha | ha | ha
    · exact ⟨0, ha⟩
    · exact ⟨1, ha⟩
    · exact ⟨2, ha⟩

/-- **Interior unification.** At a point seeing all edges CCW, the rational angle-weight
equals the integer winding (both `1`) — the per-point identity `angleWeight = winding`
on the interior, used by the regrouping. -/
lemma angleWeight_eq_winding_of_crossZ_pos (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (h : ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) :
    angleWeight P q = (P.winding (toReal q) : ℚ) := by
  rw [angleWeight_eq_one_of_crossZ_pos P hn q h, winding_eq_one_of_crossZ_pos' P hn q h]
  norm_num

/-- **Translation invariance of total corner-cross.** `∑ᵢ crossZ(vᵢ−q, vᵢ₊₁−q)` is
independent of `q` (it equals `∑ᵢ crossZ(vᵢ, vᵢ₊₁) = 2·shoelace`). For a positively
oriented polygon this total is strictly positive at *every* point — the global
orientation constraint behind the per-point sign analysis. -/
lemma sum_crossZ_sub_eq (P : LatticePolygon) (q : Pt) :
    (∑ i, crossZ (P.vert i - q) (P.vert (i + 1) - q))
      = ∑ i, crossZ (P.vert i) (P.vert (i + 1)) := by
  have key : ∀ i, crossZ (P.vert i - q) (P.vert (i + 1) - q)
      = crossZ (P.vert i) (P.vert (i + 1)) - (crossZ (P.vert i) q + crossZ q (P.vert (i + 1))) := by
    intro i; simp only [crossZ, Prod.fst_sub, Prod.snd_sub]; ring
  simp only [key]
  rw [Finset.sum_sub_distrib, sub_eq_self, Finset.sum_add_distrib]
  have hr : (∑ i, crossZ q (P.vert (i + 1))) = ∑ i, crossZ q (P.vert i) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [hr, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun i _ => by simp only [crossZ]; ring)

/-- **Orientation constraint at every point.** For a positively-oriented polygon, the
total corner-cross is strictly positive at *every* `q` (it equals `2·shoelace > 0`,
independent of `q`). Hence not all `crossZ` can be `≤ 0`: at most `n − 1` are negative. -/
lemma sum_crossZ_pos (P : LatticePolygon) (horient : P.PositivelyOriented) (q : Pt) :
    0 < ∑ j, crossZ (P.vert j - q) (P.vert (j + 1) - q) := by
  rw [sum_crossZ_sub_eq]
  have h2 : 0 < 2 * P.shoelace := by
    unfold LatticePolygon.PositivelyOriented at horient; linarith
  rw [two_shoelace_int] at h2
  have hpos : (0 : ℤ) < ∑ i, ((P.vert i).1 * (P.vert (i + 1)).2 - (P.vert i).2 * (P.vert (i + 1)).1) := by
    exact_mod_cast h2
  simpa only [crossZ] using hpos

/-- If `q` is on the wrong side of edge `v0v1` (`crossZ < 0`) but the right side of the
other two, and both `v0, v1` are above `q`, then so is `v2` (the barycentric weight on
`v2` is negative). Contrapositive: a straddling line forces the negative edge to bracket
`q.2`. -/
lemma third_above_of_neg_edge (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) (ha0 : q.2 < v0.2) (ha1 : q.2 < v1.2) :
    q.2 < v2.2 := by
  nlinarith [barycentric_y q v0 v1 v2, mul_pos h1 (sub_pos.2 ha0), mul_pos h2 (sub_pos.2 ha1), h0]

/-- Mirror: both endpoints below forces the third below. -/
lemma third_below_of_neg_edge (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) (ha0 : v0.2 < q.2) (ha1 : v1.2 < q.2) :
    v2.2 < q.2 := by
  nlinarith [barycentric_y q v0 v1 v2, mul_pos h1 (sub_pos.2 ha0), mul_pos h2 (sub_pos.2 ha1), h0]

/-- x-analog: both endpoints right of `q` forces the third right (via `barycentric_x`). -/
lemma third_right_of_neg_edge (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) (ha0 : q.1 < v0.1) (ha1 : q.1 < v1.1) :
    q.1 < v2.1 := by
  nlinarith [barycentric_x q v0 v1 v2, mul_pos h1 (sub_pos.2 ha0), mul_pos h2 (sub_pos.2 ha1), h0]

/-- x-analog: both endpoints left of `q` forces the third left. -/
lemma third_left_of_neg_edge (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) (ha0 : v0.1 < q.1) (ha1 : v1.1 < q.1) :
    v2.1 < q.1 := by
  nlinarith [barycentric_x q v0 v1 v2, mul_pos h1 (sub_pos.2 ha0), mul_pos h2 (sub_pos.2 ha1), h0]

/-- Pos-edge x-analog (for the two-negative case): if edge `v0v1` is the lone CCW edge
and both endpoints are right of `q`, the third is right too. -/
lemma third_right_of_pos_edge (q v0 v1 v2 : Pt)
    (h0 : 0 < crossZ (v0 - q) (v1 - q)) (h1 : crossZ (v1 - q) (v2 - q) < 0)
    (h2 : crossZ (v2 - q) (v0 - q) < 0) (ha0 : q.1 < v0.1) (ha1 : q.1 < v1.1) :
    q.1 < v2.1 := by
  nlinarith [barycentric_x q v0 v1 v2, mul_neg_of_neg_of_pos h1 (sub_pos.2 ha0),
    mul_neg_of_neg_of_pos h2 (sub_pos.2 ha1), h0]

/-- Pos-edge x-analog, left. -/
lemma third_left_of_pos_edge (q v0 v1 v2 : Pt)
    (h0 : 0 < crossZ (v0 - q) (v1 - q)) (h1 : crossZ (v1 - q) (v2 - q) < 0)
    (h2 : crossZ (v2 - q) (v0 - q) < 0) (ha0 : v0.1 < q.1) (ha1 : v1.1 < q.1) :
    v2.1 < q.1 := by
  nlinarith [barycentric_x q v0 v1 v2, mul_pos_of_neg_of_neg h1 (by linarith : v0.1 - q.1 < 0),
    mul_pos_of_neg_of_neg h2 (by linarith : v1.1 - q.1 < 0), h0]

/-- The negative edge is a column crossing: its endpoints lie strictly on opposite sides
of `q.1`, so its column weight is `2` (generic `q`, with an x-straddle). -/
lemma neg_edge_column_opp (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) (hg0 : v0.1 ≠ q.1) (hg1 : v1.1 ≠ q.1)
    (hlo : v0.1 < q.1 ∨ v1.1 < q.1 ∨ v2.1 < q.1)
    (hhi : q.1 < v0.1 ∨ q.1 < v1.1 ∨ q.1 < v2.1) :
    |Int.sign (v0.1 - q.1) - Int.sign (v1.1 - q.1)| = 2 := by
  have hnab : ¬ (q.1 < v0.1 ∧ q.1 < v1.1) := fun ⟨hb0, hb1⟩ => by
    have := third_right_of_neg_edge q v0 v1 v2 h0 h1 h2 hb0 hb1
    rcases hlo with h | h | h <;> linarith
  have hnbe : ¬ (v0.1 < q.1 ∧ v1.1 < q.1) := fun ⟨hb0, hb1⟩ => by
    have := third_left_of_neg_edge q v0 v1 v2 h0 h1 h2 hb0 hb1
    rcases hhi with h | h | h <;> linarith
  apply abs_sign_diff_eq_two_of_opp
  rcases lt_trichotomy v0.1 q.1 with ha | ha | ha
  · rcases lt_trichotomy v1.1 q.1 with hb | hb | hb
    · exact absurd ⟨ha, hb⟩ hnbe
    · exact absurd hb hg1
    · exact Or.inl ⟨by linarith, by linarith⟩
  · exact absurd ha hg0
  · rcases lt_trichotomy v1.1 q.1 with hb | hb | hb
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact absurd hb hg1
    · exact absurd ⟨ha, hb⟩ hnab

/-- For the two-negative case: the lone CCW edge's endpoints lie on opposite sides of
`q.1`, so its column weight is `2`. -/
lemma pos_edge_column_opp (q v0 v1 v2 : Pt)
    (h0 : 0 < crossZ (v0 - q) (v1 - q)) (h1 : crossZ (v1 - q) (v2 - q) < 0)
    (h2 : crossZ (v2 - q) (v0 - q) < 0) (hg0 : v0.1 ≠ q.1) (hg1 : v1.1 ≠ q.1)
    (hlo : v0.1 < q.1 ∨ v1.1 < q.1 ∨ v2.1 < q.1)
    (hhi : q.1 < v0.1 ∨ q.1 < v1.1 ∨ q.1 < v2.1) :
    |Int.sign (v0.1 - q.1) - Int.sign (v1.1 - q.1)| = 2 := by
  have hnab : ¬ (q.1 < v0.1 ∧ q.1 < v1.1) := fun ⟨hb0, hb1⟩ => by
    have := third_right_of_pos_edge q v0 v1 v2 h0 h1 h2 hb0 hb1
    rcases hlo with h | h | h <;> linarith
  have hnbe : ¬ (v0.1 < q.1 ∧ v1.1 < q.1) := fun ⟨hb0, hb1⟩ => by
    have := third_left_of_pos_edge q v0 v1 v2 h0 h1 h2 hb0 hb1
    rcases hhi with h | h | h <;> linarith
  apply abs_sign_diff_eq_two_of_opp
  rcases lt_trichotomy v0.1 q.1 with ha | ha | ha
  · rcases lt_trichotomy v1.1 q.1 with hb | hb | hb
    · exact absurd ⟨ha, hb⟩ hnbe
    · exact absurd hb hg1
    · exact Or.inl ⟨by linarith, by linarith⟩
  · exact absurd ha hg0
  · rcases lt_trichotomy v1.1 q.1 with hb | hb | hb
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact absurd hb hg1
    · exact absurd ⟨ha, hb⟩ hnab

/-- `≤` version: both endpoints weakly below forces the third weakly below. -/
lemma third_le_of_neg_edge (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q)) (ha0 : v0.2 ≤ q.2) (ha1 : v1.2 ≤ q.2) :
    v2.2 ≤ q.2 := by
  nlinarith [barycentric_y q v0 v1 v2, mul_nonneg h1.le (sub_nonneg.2 ha0),
    mul_nonneg h2.le (sub_nonneg.2 ha1), h0]

/-- The negative edge brackets `q.2`: with a straddling line, its crossing indicator is
exactly `1` (one endpoint weakly below, the other strictly above). -/
lemma neg_edge_crossing_eq_one (q v0 v1 v2 : Pt)
    (h0 : crossZ (v0 - q) (v1 - q) < 0) (h1 : 0 < crossZ (v1 - q) (v2 - q))
    (h2 : 0 < crossZ (v2 - q) (v0 - q))
    (hlo : v0.2 ≤ q.2 ∨ v1.2 ≤ q.2 ∨ v2.2 ≤ q.2)
    (hhi : q.2 < v0.2 ∨ q.2 < v1.2 ∨ q.2 < v2.2) :
    (if v0.2 ≤ q.2 ∧ q.2 < v1.2 then (1 : ℤ) else 0)
      + (if v1.2 ≤ q.2 ∧ q.2 < v0.2 then (1 : ℤ) else 0) = 1 := by
  have hnab : ¬ (q.2 < v0.2 ∧ q.2 < v1.2) := fun ⟨hb0, hb1⟩ => by
    have hb2 := third_above_of_neg_edge q v0 v1 v2 h0 h1 h2 hb0 hb1
    rcases hlo with hl | hl | hl <;> linarith
  have hnbe : ¬ (v0.2 ≤ q.2 ∧ v1.2 ≤ q.2) := fun ⟨hb0, hb1⟩ => by
    have hb2 := third_le_of_neg_edge q v0 v1 v2 h0 h1 h2 hb0 hb1
    rcases hhi with hh | hh | hh <;> linarith
  by_cases hv0 : v0.2 ≤ q.2 <;> by_cases hv1 : v1.2 ≤ q.2 <;> split_ifs <;> omega

/-- `univ.erase k = {k+1, k+2}` in `ZMod 3`. -/
lemma zmod3_erase : ∀ k : ZMod 3, Finset.univ.erase k = {k + 1, k + 2} := by decide

lemma zmodPn_erase (P : LatticePolygon) (hn : P.n = 3) (k : ZMod P.n) :
    Finset.univ.erase k = {k + 1, k + 2} := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_erase k

lemma zmod3_succ_ne : ∀ k : ZMod 3, k + 1 ≠ k + 2 := by decide

lemma zmod3_kk2 : ∀ k : ZMod 3, k + 2 + 2 = k + 1 := by decide

lemma zmodPn_kk2 (P : LatticePolygon) (hn : P.n = 3) (k : ZMod P.n) : k + 2 + 2 = k + 1 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_kk2 k

lemma zmod3_ne_cases : ∀ i j : ZMod 3, i ≠ j → i = j + 1 ∨ i = j + 2 := by decide

lemma zmodPn_ne_cases (P : LatticePolygon) (hn : P.n = 3) (i j : ZMod P.n) (h : i ≠ j) :
    i = j + 1 ∨ i = j + 2 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_ne_cases i j h

/-- A sum over the two non-`k` edges of a triangle. -/
lemma sum_erase_zmodPn {M : Type*} [AddCommMonoid M] (P : LatticePolygon) (hn : P.n = 3)
    (k : ZMod P.n) (f : ZMod P.n → M) :
    ∑ j ∈ Finset.univ.erase k, f j = f (k + 1) + f (k + 2) := by
  have hne : k + 1 ≠ k + 2 := by
    obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_succ_ne k
  rw [zmodPn_erase P hn k, Finset.sum_pair hne]

/-- The full triangle sum starting at any vertex `k`. -/
lemma sum_zmodPn_shift {M : Type*} [AddCommMonoid M] (P : LatticePolygon) (hn : P.n = 3)
    (k : ZMod P.n) (f : ZMod P.n → M) : (∑ j, f j) = f k + f (k + 1) + f (k + 2) := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ k), sum_erase_zmodPn P hn k, ← add_assoc]

/-- `k`-relative `ZMod 3` index identities. -/
lemma zmod3_krel : ∀ k : ZMod 3,
    ((k + 2) + 1 = k) ∧ (k + 1 ≠ k) ∧ (k + 2 ≠ k) ∧ ((k + 1) + 1 = k + 2) := by decide

lemma zmodPn_krel (P : LatticePolygon) (hn : P.n = 3) (k : ZMod P.n) :
    ((k + 2) + 1 = k) ∧ (k + 1 ≠ k) ∧ (k + 2 ≠ k) ∧ ((k + 1) + 1 = k + 2) := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_krel k

lemma zmod3_krel3 : ∀ k : ZMod 3, ((k + 1) + 2 = k) ∧ ((k + 2) + 2 = k + 1) := by decide

lemma zmodPn_krel3 (P : LatticePolygon) (hn : P.n = 3) (k : ZMod P.n) :
    ((k + 1) + 2 = k) ∧ ((k + 2) + 2 = k + 1) := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_krel3 k

/-- `{k, k+1, k+2}` covers `ZMod 3`. -/
lemma zmod3_cover : ∀ k j : ZMod 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by decide

lemma zmodPn_cover (P : LatticePolygon) (hn : P.n = 3) (k j : ZMod P.n) :
    j = k ∨ j = k + 1 ∨ j = k + 2 := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_cover k j

/-- At every point, some edge is seen CCW (`crossZ > 0`) — a positive sum forces a
positive term. So a point can be on the wrong side of at most `n − 1` edges. -/
lemma exists_crossZ_pos (P : LatticePolygon) (horient : P.PositivelyOriented) (q : Pt) :
    ∃ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) := by
  by_contra h
  push_neg at h
  have hp := sum_crossZ_pos P horient q
  have hle : (∑ j, crossZ (P.vert j - q) (P.vert (j + 1) - q)) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => h j)
  linarith

/-- If edge `k` is on `q`'s line, some *other* edge is seen CCW. -/
lemma exists_other_crossZ_pos (P : LatticePolygon) (horient : P.PositivelyOriented) (q : Pt)
    (k : ZMod P.n) (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0) :
    ∃ j, j ≠ k ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) := by
  obtain ⟨j, hj⟩ := exists_crossZ_pos P horient q
  refine ⟨j, ?_, hj⟩
  rintro rfl
  rw [h0] at hj
  exact absurd hj (lt_irrefl 0)

/-- **Converse, one-negative case.** If `q` is on the wrong side of exactly edge `k`
(others CCW) with a vertically straddled column, `winding = 0` (≠ 1): the negative edge
brackets `q.2`, so `winding = 1 − 1 = 0`. -/
lemma winding_eq_zero_of_one_neg (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0)
    (hi : ∀ j, j ≠ k → 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q))
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    P.winding (toReal q) = 0 := by
  obtain ⟨ek, hk1, hk2, ek12⟩ := zmodPn_krel P hn k
  have h1 := hi (k + 1) hk1; rw [ek12] at h1
  have h2 := hi (k + 2) hk2; rw [ek] at h2
  have hlo3 : (P.vert k).2 ≤ q.2 ∨ (P.vert (k + 1)).2 ≤ q.2 ∨ (P.vert (k + 2)).2 ≤ q.2 := by
    obtain ⟨j, hj⟩ := hlo
    rcases zmodPn_cover P hn k j with h | h | h <;> subst h
    exacts [Or.inl hj, Or.inr (Or.inl hj), Or.inr (Or.inr hj)]
  have hhi3 : q.2 < (P.vert k).2 ∨ q.2 < (P.vert (k + 1)).2 ∨ q.2 < (P.vert (k + 2)).2 := by
    obtain ⟨j, hj⟩ := hhi
    rcases zmodPn_cover P hn k j with h | h | h <;> subst h
    exacts [Or.inl hj, Or.inr (Or.inl hj), Or.inr (Or.inr hj)]
  rw [winding_one_neg_eq P hn q k hk hi hlo hhi,
    neg_edge_crossing_eq_one q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2)) hk h1 h2 hlo3 hhi3]
  norm_num

/-- **Converse, two-negative case.** On the wrong side of two edges (only edge `c` CCW),
with a straddled column, `winding ≤ 0` (≠ 1): `winding = up_c + down_c − 1 ≤ 0` since an
edge crosses the line at most once. -/
lemma winding_le_zero_of_two_neg (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (c : ZMod P.n)
    (hc : 0 < crossZ (P.vert c - q) (P.vert (c + 1) - q))
    (hi : ∀ j, j ≠ c → crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0)
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    P.winding (toReal q) ≤ 0 := by
  have hdown : (∑ j, (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0)) = 1 := by
    have htot := sum_crossing_eq_two P hn q hlo hhi
    have hbal := sum_upward_eq_downward P q
    rw [Finset.sum_add_distrib, hbal] at htot
    omega
  rw [winding_of_two_crossZ_neg P q c hc hi, Finset.sum_erase_eq_sub (Finset.mem_univ c), hdown]
  have hle : (if (P.vert c).2 ≤ q.2 ∧ q.2 < (P.vert (c + 1)).2 then (1 : ℤ) else 0)
      + (if (P.vert (c + 1)).2 ≤ q.2 ∧ q.2 < (P.vert c).2 then (1 : ℤ) else 0) ≤ 1 := by
    split_ifs <;> omega
  omega

/-- Three distinct elements cover `ZMod 3`. -/
lemma zmod3_cover3 : ∀ a b c j : ZMod 3, a ≠ b → b ≠ c → a ≠ c → (j = a ∨ j = b ∨ j = c) := by
  decide

lemma zmodPn_cover3 (P : LatticePolygon) (hn : P.n = 3) (a b c j : ZMod P.n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : j = a ∨ j = b ∨ j = c := by
  obtain ⟨n, pos, vert⟩ := P; subst hn; exact zmod3_cover3 a b c j hab hbc hac

/-- A point with `winding = 1` has its column-height vertically straddled (else it is
above or below every vertex, giving `winding = 0`). -/
lemma y_straddle_of_winding_one (P : LatticePolygon) (q : Pt) (hw : P.winding (toReal q) = 1) :
    (∃ j, (P.vert j).2 ≤ q.2) ∧ (∃ j, q.2 < (P.vert j).2) := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    rw [winding_eq_zero_of_below P (toReal q) (fun i => by simp only [toReal]; exact_mod_cast h i)] at hw
    exact absurd hw (by norm_num)
  · by_contra h
    push_neg at h
    rw [winding_eq_zero_of_above P (toReal q) (fun i => by simp only [toReal]; exact_mod_cast h i)] at hw
    exact absurd hw (by norm_num)

/-- The horizontal analog: a `winding = 1` point is horizontally straddled (some vertex
weakly left, some weakly right). With `y_straddle_of_winding_one`, interior lattice
points lie in the vertex bounding box, hence form a finite set. -/
lemma x_straddle_of_winding_one (P : LatticePolygon) (q : Pt) (hw : P.winding (toReal q) = 1) :
    (∃ j, (P.vert j).1 ≤ q.1) ∧ (∃ j, q.1 ≤ (P.vert j).1) := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    rw [winding_eq_zero_of_left P (toReal q) (fun i => by simp only [toReal]; exact_mod_cast h i)] at hw
    exact absurd hw (by norm_num)
  · by_contra h
    push_neg at h
    rw [winding_eq_zero_of_right P (toReal q) (fun i => by simp only [toReal]; exact_mod_cast h i)] at hw
    exact absurd hw (by norm_num)

/-- **Converse.** A `winding = 1` point off every edge line (`all crossZ ≠ 0`) sees all
edges CCW (`all crossZ > 0`). Otherwise it is wrong-side of `1` or `2` edges, giving
`winding ≤ 0 ≠ 1`. With the forward bridge this yields `{winding=1, off-line} =
{crossZ-interior}`. -/
lemma all_crossZ_pos_of_winding_one (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hw : P.winding (toReal q) = 1)
    (hne : ∀ j, crossZ (P.vert j - q) (P.vert (j + 1) - q) ≠ 0) :
    ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) := by
  obtain ⟨hlo, hhi⟩ := y_straddle_of_winding_one P q hw
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk⟩ := hcon
  have hkneg : crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0 := lt_of_le_of_ne hk (hne k)
  by_cases hother : ∀ j, j ≠ k → 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)
  · rw [winding_eq_zero_of_one_neg P hn q k hkneg hother hlo hhi] at hw
    exact absurd hw (by norm_num)
  · push_neg at hother
    obtain ⟨m, hmk, hm⟩ := hother
    have hmneg : crossZ (P.vert m - q) (P.vert (m + 1) - q) < 0 := lt_of_le_of_ne hm (hne m)
    obtain ⟨c, hc⟩ := exists_crossZ_pos P horient q
    have hck : c ≠ k := fun h => by rw [h] at hc; linarith
    have hcm : c ≠ m := fun h => by rw [h] at hc; linarith
    have hi2 : ∀ j, j ≠ c → crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 := by
      intro j hjc
      rcases zmodPn_cover3 P hn c k m j hck (Ne.symm hmk) hcm with h | h | h
      · exact absurd h hjc
      · rw [h]; exact hkneg
      · rw [h]; exact hmneg
    have hwle := winding_le_zero_of_two_neg P hn q c hc hi2 hlo hhi
    rw [hw] at hwle
    exact absurd hwle (by norm_num)

/-- A point seeing all edges CCW is an interior lattice point (`winding = 1` and
off-boundary). The reverse inclusion is `all_crossZ_pos_of_winding_one`, so
`interiorLattice = {q | all crossZ > 0}`. -/
lemma mem_interiorLattice_of_crossZ_pos (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (h : ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) :
    q ∈ P.interiorLattice :=
  ⟨winding_eq_one_of_crossZ_pos' P hn q h, not_mem_boundary_of_crossZ_ne P q (fun k => (h k).ne')⟩

/-- An edge crosses a horizontal line at most once (up and down brackets are exclusive). -/
lemma edge_crossing_le_one (P : LatticePolygon) (q : Pt) (j : ZMod P.n) :
    (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0)
      + (if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0) ≤ 1 := by
  split_ifs <;> omega

/-- Each edge's winding contribution is at most its upward-crossing indicator. -/
lemma wind_term_le_up (P : LatticePolygon) (q : Pt) (j : ZMod P.n) :
    (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
          ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
          ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0)
      ≤ (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0) := by
  split_ifs <;> omega

/-- A CCW edge (`crossZ > 0`) contributes its upward-crossing indicator to the winding. -/
lemma wind_term_eq_up_of_pos (P : LatticePolygon) (q : Pt) (j : ZMod P.n)
    (h : 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q)) :
    (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
          ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
          ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0)
      = (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0) := by
  split_ifs <;> omega

/-- A non-CCW edge (`crossZ < 0`) contributes minus its downward-crossing indicator. -/
lemma wind_term_eq_neg_down_of_neg (P : LatticePolygon) (q : Pt) (j : ZMod P.n)
    (h : crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0) :
    (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
          ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
          ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0)
      = -(if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2 then (1 : ℤ) else 0) := by
  split_ifs <;> omega

/-- An edge on `q`'s line (`crossZ = 0`) contributes exactly `0` to the winding. -/
lemma wind_term_eq_zero (P : LatticePolygon) (q : Pt) (j : ZMod P.n)
    (h : crossZ (P.vert j - q) (P.vert (j + 1) - q) = 0) :
    (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
          ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
          ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0) = 0 := by
  split_ifs <;> omega

/-- When edge `k` is on `q`'s line (`crossZ_k = 0`), it drops from the winding sum. -/
lemma winding_of_crossZ_zero (P : LatticePolygon) (q : Pt) (k : ZMod P.n)
    (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0) :
    P.winding (toReal q) = ∑ j ∈ Finset.univ.erase k,
      (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
            ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
            ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0) := by
  rw [winding_toReal_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    wind_term_eq_zero P q k h0, zero_add]

/-- An interior point (`winding = 1`) on edge `k`'s line does not up-bracket edge `k`:
otherwise `winding ≤ 1 − 1 = 0`. -/
lemma not_up_of_winding_crossZ_zero (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hw : P.winding (toReal q) = 1) (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    ¬ ((P.vert k).2 ≤ q.2 ∧ q.2 < (P.vert (k + 1)).2) := by
  have hup : (∑ j, (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0)) = 1 := by
    have htot := sum_crossing_eq_two P hn q hlo hhi
    have hbal := sum_upward_eq_downward P q
    rw [Finset.sum_add_distrib, ← hbal] at htot
    omega
  have hub : P.winding (toReal q)
      ≤ 1 - (if (P.vert k).2 ≤ q.2 ∧ q.2 < (P.vert (k + 1)).2 then (1 : ℤ) else 0) := by
    rw [winding_of_crossZ_zero P q k h0]
    have key : (∑ j ∈ Finset.univ.erase k,
          (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0))
        = 1 - (if (P.vert k).2 ≤ q.2 ∧ q.2 < (P.vert (k + 1)).2 then (1 : ℤ) else 0) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hup]
    rw [← key]
    exact Finset.sum_le_sum (fun j _ => wind_term_le_up P q j)
  intro hbr
  rw [hw, if_pos hbr] at hub
  linarith

/-- Winding value when edge `k` is on the line, edge `k+1` is CCW, and edge `k+2` is
non-CCW: the upward crossing of `k+1` minus the downward crossing of `k+2`. -/
lemma winding_zero_pos_neg (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : 0 < crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
    (h2 : crossZ (P.vert (k + 2) - q) (P.vert k - q) < 0) :
    P.winding (toReal q)
      = (if (P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert (k + 2)).2 then (1 : ℤ) else 0)
        - (if (P.vert k).2 ≤ q.2 ∧ q.2 < (P.vert (k + 2)).2 then (1 : ℤ) else 0) := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  rw [winding_of_crossZ_zero P q k h0, sum_erase_zmodPn P hn k,
    wind_term_eq_up_of_pos P q (k + 1) (by rw [ek12]; exact h1),
    wind_term_eq_neg_down_of_neg P q (k + 2) (by rw [ek]; exact h2), ek12, ek]
  ring

/-- Winding value when edge `k` is on the line, edge `k+1` is non-CCW, and edge `k+2` is
CCW: the upward crossing of `k+2` minus the downward crossing of `k+1`. -/
lemma winding_zero_neg_pos (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q) < 0)
    (h2 : 0 < crossZ (P.vert (k + 2) - q) (P.vert k - q)) :
    P.winding (toReal q)
      = (if (P.vert (k + 2)).2 ≤ q.2 ∧ q.2 < (P.vert k).2 then (1 : ℤ) else 0)
        - (if (P.vert (k + 2)).2 ≤ q.2 ∧ q.2 < (P.vert (k + 1)).2 then (1 : ℤ) else 0) := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  rw [winding_of_crossZ_zero P q k h0, sum_erase_zmodPn P hn k,
    wind_term_eq_neg_down_of_neg P q (k + 1) (by rw [ek12]; exact h1),
    wind_term_eq_up_of_pos P q (k + 2) (by rw [ek]; exact h2), ek12, ek]
  ring

/-- The `{0,+,−}` no-down-bracket case is contradictory at `winding = 1`: balance forces
edge `k+1` to both up- and down-cross, impossible. -/
lemma winding_zero_pos_neg_contra (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hw : P.winding (toReal q) = 1) (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : 0 < crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
    (h2 : crossZ (P.vert (k + 2) - q) (P.vert k - q) < 0)
    (hnd : ¬ ((P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert k).2))
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) : False := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  have hwv := winding_zero_pos_neg P hn q k h0 h1 h2
  rw [hw] at hwv
  have hds := down_sum_eq_one P hn q hlo hhi
  rw [sum_zmodPn_shift P hn k, ek12, ek, if_neg hnd] at hds
  have hec := edge_crossing_le_one P q (k + 1)
  rw [ek12] at hec
  omega

/-- The `{0,−,+}` no-down-bracket case is contradictory at `winding = 1`: balance forces
edge `k+2` to both up- and down-cross, impossible. -/
lemma winding_zero_neg_pos_contra (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hw : P.winding (toReal q) = 1) (h0 : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q) < 0)
    (h2 : 0 < crossZ (P.vert (k + 2) - q) (P.vert k - q))
    (hnd : ¬ ((P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert k).2))
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) : False := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  have hwv := winding_zero_neg_pos P hn q k h0 h1 h2
  rw [hw] at hwv
  have hds := down_sum_eq_one P hn q hlo hhi
  rw [sum_zmodPn_shift P hn k, ek12, ek, if_neg hnd] at hds
  have hec := edge_crossing_le_one P q (k + 2)
  rw [ek] at hec
  omega

/-- **Corner non-degeneracy** (integer form): the corner cross at vertex `k+1` is nonzero
for a positively-oriented triangle. -/
lemma corner_crossZ_ne (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented)
    (k : ZMod P.n) :
    crossZ (P.vert k - P.vert (k + 1)) (P.vert (k + 2) - P.vert (k + 1)) ≠ 0 := by
  intro h
  have hp := corner_cross_base_pos P hn horient (k + 2)
  obtain ⟨ek, _, _, _⟩ := zmodPn_krel P hn k
  have ekm1 : (k + 2) - 1 = k + 1 := by ring
  rw [ekm1, ek] at hp
  have hcast : cross (toReal (P.vert (k + 2)) - toReal (P.vert (k + 1)))
      (toReal (P.vert k) - toReal (P.vert (k + 1)))
      = ((crossZ (P.vert (k + 2) - P.vert (k + 1)) (P.vert k - P.vert (k + 1)) : ℤ) : ℝ) := by
    simp only [cross, crossZ, toReal, Prod.fst_sub, Prod.snd_sub]
    push_cast; ring
  rw [hcast] at hp
  have hanti : crossZ (P.vert (k + 2) - P.vert (k + 1)) (P.vert k - P.vert (k + 1))
      = - crossZ (P.vert k - P.vert (k + 1)) (P.vert (k + 2) - P.vert (k + 1)) := by
    simp only [crossZ]; ring
  rw [hanti, h] at hp
  simp at hp

/-- Corner non-degeneracy at vertex `v_k` (the other adjacent corner). -/
lemma corner_crossZ_ne2 (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented)
    (k : ZMod P.n) :
    crossZ (P.vert (k + 2) - P.vert k) (P.vert (k + 1) - P.vert k) ≠ 0 := by
  have h := corner_crossZ_ne P hn horient (k + 2)
  obtain ⟨ek, _, _, _⟩ := zmodPn_krel P hn k
  rw [ek, zmodPn_kk2 P hn k] at h
  exact h

/-- **Interior ⟹ off every edge line.** An interior lattice point of a positively-oriented
triangle sees no edge on its own line (`all crossZ ≠ 0`). All cases of `crossZ_k = 0` are
contradictory: edge `k` brackets `q` (on-segment), the other edges force a winding/sum
contradiction, or `q` is a shared vertex (on-segment). -/
lemma crossZ_ne_zero_of_mem_interiorLattice (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hq : q ∈ P.interiorLattice) (k : ZMod P.n) :
    crossZ (P.vert k - q) (P.vert (k + 1) - q) ≠ 0 := by
  intro h0
  obtain ⟨hw, hbdry⟩ := hq
  obtain ⟨hlo, hhi⟩ := y_straddle_of_winding_one P q hw
  by_cases hup : (P.vert k).2 ≤ q.2 ∧ q.2 < (P.vert (k + 1)).2
  · exact hbdry (Set.mem_iUnion.2 ⟨k, mem_edgeSeg_of_bracket P q k h0 hup.1 hup.2⟩)
  by_cases hdn : (P.vert (k + 1)).2 ≤ q.2 ∧ q.2 < (P.vert k).2
  · exact hbdry (Set.mem_iUnion.2 ⟨k, mem_edgeSeg_of_bracket' P q k h0 hdn.1 hdn.2⟩)
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  have hsum := sum_crossZ_pos P horient q
  rw [sum_zmodPn_shift P hn k, ek12, ek, h0, zero_add] at hsum
  rcases lt_trichotomy (crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q)) 0 with hc1 | hc1 | hc1
  · rcases lt_trichotomy (crossZ (P.vert (k + 2) - q) (P.vert k - q)) 0 with hc2 | hc2 | hc2
    · linarith
    · linarith
    · exact winding_zero_neg_pos_contra P hn q k hw h0 hc1 hc2 hdn hlo hhi
  · have hqv : q = P.vert (k + 1) :=
      eq_vertex_of_adjacent_crossZ_zero q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2)) h0 hc1
        (corner_crossZ_ne P hn horient k)
    exact hbdry (Set.mem_iUnion.2 ⟨k, by rw [hqv]; exact right_mem_segment ℝ _ _⟩)
  · rcases lt_trichotomy (crossZ (P.vert (k + 2) - q) (P.vert k - q)) 0 with hc2 | hc2 | hc2
    · exact winding_zero_pos_neg_contra P hn q k hw h0 hc1 hc2 hdn hlo hhi
    · have hqv : q = P.vert k :=
        eq_vertex_of_adjacent_crossZ_zero q (P.vert (k + 2)) (P.vert k) (P.vert (k + 1)) hc2 h0
          (corner_crossZ_ne2 P hn horient k)
      exact hbdry (Set.mem_iUnion.2 ⟨k, by rw [hqv]; exact left_mem_segment ℝ _ _⟩)
    · exact not_crossZ_zero_others_pos P q k hbdry h0 hc1 hc2

/-- An edge seen non-CCW (`crossZ ≤ 0`) contributes at most `0` to the winding. -/
lemma wind_term_le_zero (P : LatticePolygon) (q : Pt) (j : ZMod P.n)
    (h : crossZ (P.vert j - q) (P.vert (j + 1) - q) ≤ 0) :
    (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2
          ∧ 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) then (1 : ℤ)
        else if (P.vert (j + 1)).2 ≤ q.2 ∧ q.2 < (P.vert j).2
          ∧ crossZ (P.vert j - q) (P.vert (j + 1) - q) < 0 then -1 else 0) ≤ 0 := by
  split_ifs <;> omega

/-- The winding number is at most `1` at a vertically straddled point: each edge's signed
contribution is at most its upward-crossing indicator, and those sum to `1`. -/
lemma winding_le_one (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (hlo : ∃ j, (P.vert j).2 ≤ q.2) (hhi : ∃ j, q.2 < (P.vert j).2) :
    P.winding (toReal q) ≤ 1 := by
  rw [winding_toReal_eq]
  have hup : (∑ j, (if (P.vert j).2 ≤ q.2 ∧ q.2 < (P.vert (j + 1)).2 then (1 : ℤ) else 0)) = 1 := by
    have htot := sum_crossing_eq_two P hn q hlo hhi
    have hbal := sum_upward_eq_downward P q
    rw [Finset.sum_add_distrib, ← hbal] at htot
    omega
  rw [← hup]
  refine Finset.sum_le_sum (fun j _ => ?_)
  split_ifs <;> omega

/-- Converse for interior lattice points off every edge line: they see all edges CCW.
Combined with `mem_interiorLattice_of_crossZ_pos`, this is `interiorLattice =
{q | all crossZ > 0}` on the off-line part (interior points are never on an edge line). -/
lemma all_crossZ_pos_of_mem_interiorLattice (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hq : q ∈ P.interiorLattice)
    (hne : ∀ j, crossZ (P.vert j - q) (P.vert (j + 1) - q) ≠ 0) :
    ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) :=
  all_crossZ_pos_of_winding_one P hn horient q hq.1 hne

/-- **Interior ⟹ all edges CCW.** An interior lattice point of a positively-oriented
triangle sees every edge counterclockwise (`crossZ > 0`). -/
lemma crossZ_pos_of_mem_interiorLattice (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hq : q ∈ P.interiorLattice) (k : ZMod P.n) :
    0 < crossZ (P.vert k - q) (P.vert (k + 1) - q) :=
  all_crossZ_pos_of_mem_interiorLattice P hn horient q hq
    (fun j => crossZ_ne_zero_of_mem_interiorLattice P hn horient q hq j) k

/-- **`angleWeight = 1` at interior lattice points.** Combined with `crossZ_pos`, the
fractional winding `angleWeight` is exactly `1` on `interiorLattice`. -/
lemma angleWeight_eq_one_of_mem_interiorLattice (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hq : q ∈ P.interiorLattice) :
    angleWeight P q = 1 :=
  angleWeight_eq_one_of_crossZ_pos P hn q
    (fun k => crossZ_pos_of_mem_interiorLattice P hn horient q hq k)

/-- **Full interior characterization (triangle).** `q` is an interior lattice point iff it
sees every edge CCW — unconditionally (no off-line hypothesis needed). -/
lemma mem_interiorLattice_iff_crossZ_pos (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) :
    q ∈ P.interiorLattice ↔ ∀ k, 0 < crossZ (P.vert k - q) (P.vert (k + 1) - q) :=
  ⟨fun hq k => crossZ_pos_of_mem_interiorLattice P hn horient q hq k,
    mem_interiorLattice_of_crossZ_pos P hn q⟩

/-- If the three triangle edges are all CCW (`crossZ > 0` at edges `0,1,2`), `q` is an
interior lattice point. -/
lemma mem_interiorLattice_of_three_pos (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (h0 : 0 < crossZ (P.vert 0 - q) (P.vert 1 - q))
    (h1 : 0 < crossZ (P.vert 1 - q) (P.vert 2 - q))
    (h2 : 0 < crossZ (P.vert 2 - q) (P.vert 0 - q)) :
    q ∈ P.interiorLattice := by
  obtain ⟨ea, eb, ec, _, _, _⟩ := zmodPn_idx P hn
  refine mem_interiorLattice_of_crossZ_pos P hn q (fun k => ?_)
  rcases zmodPn_cases P hn k with rfl | rfl | rfl
  · rw [ea]; exact h0
  · rw [eb]; exact h1
  · rw [ec]; exact h2

/-- A non-interior lattice point sees some edge non-CCW (`crossZ ≤ 0`). -/
lemma exists_crossZ_nonpos_of_not_mem (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hint : q ∉ P.interiorLattice) :
    ∃ k, crossZ (P.vert k - q) (P.vert (k + 1) - q) ≤ 0 := by
  by_contra h
  push_neg at h
  exact hint ((mem_interiorLattice_iff_crossZ_pos P hn horient q).2 h)

/-- **On-edge ⟹ adjacent edge CCW.** A lattice point on edge `j` (not the far vertex)
sees the next edge counterclockwise: `crossZ_{j+1} = a · corner ≥ 0`, nonzero unless `q`
is the shared vertex. -/
lemma crossZ_next_pos_of_mem_edgeSeg (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (j : ZMod P.n)
    (hmem : toReal q ∈ P.edgeSeg j) (hne : q ≠ P.vert (j + 1)) :
    0 < crossZ (P.vert (j + 1) - q) (P.vert (j + 2) - q) := by
  have hj : crossZ (P.vert j - q) (P.vert (j + 1) - q) = 0 :=
    crossZ_eq_zero_of_mem_edgeSeg P q j hmem
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hmem
  obtain ⟨t, ht, hqt⟩ := hmem
  have hcross := cross_next_eq_smul_corner (toReal (P.vert j)) (toReal (P.vert (j + 1)))
    (toReal (P.vert (j + 2))) (toReal q) (1 - t) t (by ring) hqt.symm
  have hcorner := corner_cross_base_pos P hn horient (j + 1)
  have e1 : (j + 1) - 1 = j := by ring
  have e2 : (j + 1) + 1 = j + 2 := by ring
  rw [e1, e2] at hcorner
  have hge : (0 : ℝ) ≤ cross (toReal (P.vert (j + 1)) - toReal q)
      (toReal (P.vert (j + 2)) - toReal q) := by
    rw [hcross]; exact mul_nonneg (by linarith [ht.2]) hcorner.le
  have hcast : cross (toReal (P.vert (j + 1)) - toReal q) (toReal (P.vert (j + 2)) - toReal q)
      = ((crossZ (P.vert (j + 1) - q) (P.vert (j + 2) - q) : ℤ) : ℝ) := by
    simp only [cross, crossZ, toReal, Prod.fst_sub, Prod.snd_sub]; push_cast; ring
  rw [hcast] at hge
  have hge' : 0 ≤ crossZ (P.vert (j + 1) - q) (P.vert (j + 2) - q) := by exact_mod_cast hge
  rcases hge'.lt_or_eq with h | h
  · exact h
  · exact absurd (eq_vertex_of_adjacent_crossZ_zero q (P.vert j) (P.vert (j + 1)) (P.vert (j + 2))
      hj h.symm (corner_crossZ_ne P hn horient j)) hne

/-- **On-edge ⟹ previous edge CCW.** Symmetric companion: a lattice point on edge `j`
(not the near vertex `vⱼ`) sees the previous edge `j+2` counterclockwise. -/
lemma crossZ_prev_pos_of_mem_edgeSeg (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (j : ZMod P.n)
    (hmem : toReal q ∈ P.edgeSeg j) (hne : q ≠ P.vert j) :
    0 < crossZ (P.vert (j + 2) - q) (P.vert j - q) := by
  have hj : crossZ (P.vert j - q) (P.vert (j + 1) - q) = 0 :=
    crossZ_eq_zero_of_mem_edgeSeg P q j hmem
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hmem
  obtain ⟨t, ht, hqt⟩ := hmem
  have hcross := cross_prev_eq_smul_corner (toReal (P.vert j)) (toReal (P.vert (j + 1)))
    (toReal (P.vert (j + 2))) (toReal q) (1 - t) t (by ring) hqt.symm
  obtain ⟨ek, _, _, _⟩ := zmodPn_krel P hn j
  have hcorner := corner_cross_base_pos P hn horient (j + 2)
  have e1 : (j + 2) - 1 = j + 1 := by ring
  rw [e1, ek] at hcorner
  have hge : (0 : ℝ) ≤ cross (toReal (P.vert (j + 2)) - toReal q) (toReal (P.vert j) - toReal q) := by
    rw [cross_skew, hcross,
      cross_skew (toReal (P.vert j) - toReal (P.vert (j + 1)))
        (toReal (P.vert (j + 2)) - toReal (P.vert (j + 1)))]
    nlinarith [hcorner, ht.1]
  have hcast : cross (toReal (P.vert (j + 2)) - toReal q) (toReal (P.vert j) - toReal q)
      = ((crossZ (P.vert (j + 2) - q) (P.vert j - q) : ℤ) : ℝ) := by
    simp only [cross, crossZ, toReal, Prod.fst_sub, Prod.snd_sub]; push_cast; ring
  rw [hcast] at hge
  have hge' : 0 ≤ crossZ (P.vert (j + 2) - q) (P.vert j - q) := by exact_mod_cast hge
  rcases hge'.lt_or_eq with h | h
  · exact h
  · exact absurd (eq_vertex_of_adjacent_crossZ_zero q (P.vert (j + 2)) (P.vert j) (P.vert (j + 1))
      h.symm hj (corner_crossZ_ne2 P hn horient j)) hne

/-- **On-edge ⟹ all other edges CCW.** An edge-interior lattice point (`q` on edge `j`,
not a vertex) sees every other edge counterclockwise — the all-others-CCW hypothesis of
`angleWeight_edge_triangle`. -/
lemma others_crossZ_pos_of_mem_edgeSeg (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (j : ZMod P.n)
    (hmem : toReal q ∈ P.edgeSeg j) (hne0 : q ≠ P.vert j) (hne1 : q ≠ P.vert (j + 1))
    (i : ZMod P.n) (hij : i ≠ j) :
    0 < crossZ (P.vert i - q) (P.vert (i + 1) - q) := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn j
  rcases zmodPn_ne_cases P hn i j hij with h | h
  · subst h; rw [ek12]; exact crossZ_next_pos_of_mem_edgeSeg P hn horient q j hmem hne1
  · subst h; rw [ek]; exact crossZ_prev_pos_of_mem_edgeSeg P hn horient q j hmem hne0

/-- An edge-interior lattice point (`q` on edge `j`, distinct from both endpoints) is a
*strict* convex combination of the endpoints (`t ∈ (0,1)`). -/
lemma exists_t_Ioo_of_mem_edgeSeg (P : LatticePolygon) (q : Pt) (j : ZMod P.n)
    (hmem : toReal q ∈ P.edgeSeg j) (hne0 : q ≠ P.vert j) (hne1 : q ≠ P.vert (j + 1)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      toReal q = (1 - t) • toReal (P.vert j) + t • toReal (P.vert (j + 1)) := by
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hmem
  obtain ⟨t, ht, hqt⟩ := hmem
  refine ⟨t, ?_, ?_, hqt.symm⟩
  · rcases ht.1.lt_or_eq with h | h
    · exact h
    · exact absurd (toReal_injective (by rw [← hqt, ← h]; simp)) hne0
  · rcases ht.2.lt_or_eq with h | h
    · exact h
    · exact absurd (toReal_injective (by rw [← hqt, h]; simp)) hne1

/-- A positive real scaling preserves integer signs. -/
lemma sign_eq_of_real_eq_pos_mul {x y : ℤ} {s : ℝ} (hs : 0 < s) (h : (x : ℝ) = s * y) :
    Int.sign x = Int.sign y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have : (x : ℝ) < 0 := by rw [h]; exact mul_neg_of_pos_of_neg hs (by exact_mod_cast hy)
    rw [Int.sign_eq_neg_one_of_neg (by exact_mod_cast this), Int.sign_eq_neg_one_of_neg hy]
  · rw [hy] at h; simp only [Int.cast_zero, mul_zero] at h
    rw [show x = 0 by exact_mod_cast h, hy]
  · have : (0 : ℝ) < x := by rw [h]; exact mul_pos hs (by exact_mod_cast hy)
    rw [Int.sign_eq_one_of_pos (by exact_mod_cast this), Int.sign_eq_one_of_pos hy]

/-- The x-signs of an edge's endpoints, seen from an interior point of that edge, are
negatives of each other (`q.1` lies weakly between, strictly for non-vertical edges). -/
lemma sign_fst_sum_of_mem_edgeSeg (P : LatticePolygon) (q : Pt) (j : ZMod P.n)
    (hmem : toReal q ∈ P.edgeSeg j) (hne0 : q ≠ P.vert j) (hne1 : q ≠ P.vert (j + 1)) :
    Int.sign (P.vert j - q).1 + Int.sign (P.vert (j + 1) - q).1 = 0 := by
  obtain ⟨t, ht0, ht1, hqt⟩ := exists_t_Ioo_of_mem_edgeSeg P q j hmem hne0 hne1
  obtain ⟨hl, hr⟩ := fst_sub_of_combo (toReal (P.vert j)) (toReal (P.vert (j + 1))) (toReal q) t hqt
  have ea : ((P.vert j - q).1 : ℝ) = t * ((P.vert j - P.vert (j + 1)).1 : ℝ) := by
    have e1 : ((P.vert j - q).1 : ℝ) = (toReal (P.vert j) - toReal q).1 := by
      simp only [toReal, Prod.fst_sub]; push_cast; ring
    rw [e1, hl]; simp only [toReal, Prod.fst_sub]; push_cast; ring
  have eb : ((P.vert (j + 1) - q).1 : ℝ) = (1 - t) * ((P.vert (j + 1) - P.vert j).1 : ℝ) := by
    have e1 : ((P.vert (j + 1) - q).1 : ℝ) = (toReal (P.vert (j + 1)) - toReal q).1 := by
      simp only [toReal, Prod.fst_sub]; push_cast; ring
    rw [e1, hr]; simp only [toReal, Prod.fst_sub]; push_cast; ring
  rw [sign_eq_of_real_eq_pos_mul ht0 ea, sign_eq_of_real_eq_pos_mul (by linarith : (0:ℝ) < 1 - t) eb]
  have hneg : (P.vert (j + 1) - P.vert j).1 = -(P.vert j - P.vert (j + 1)).1 := by
    simp only [Prod.fst_sub]; ring
  rw [hneg, Int.sign_neg]; ring

/-- The adjacent column-crossings of an edge-interior lattice point total `2` (the
`hsum` hypothesis of the boundary value). The two endpoint x-signs are opposite (or both
zero on a vertical edge, where the third vertex is off the line by non-degeneracy). -/
lemma hsum_of_mem_edgeSeg (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented)
    (q : Pt) (j : ZMod P.n) (hmem : toReal q ∈ P.edgeSeg j)
    (hne0 : q ≠ P.vert j) (hne1 : q ≠ P.vert (j + 1)) :
    |Int.sign (P.vert (j + 1) - q).1 - Int.sign (P.vert (j + 2) - q).1|
      + |Int.sign (P.vert (j + 2) - q).1 - Int.sign (P.vert j - q).1| = 2 := by
  have hsign := sign_fst_sum_of_mem_edgeSeg P q j hmem hne0 hne1
  have hnd : Int.sign (P.vert j - q).1 = 0 → Int.sign (P.vert (j + 2) - q).1 ≠ 0 := by
    intro h0 h2
    apply corner_crossZ_ne P hn horient j
    have ej : (P.vert j).1 = q.1 := by
      have := Int.sign_eq_zero_iff_zero.mp h0; simp only [Prod.fst_sub] at this; omega
    have ej1 : (P.vert (j + 1)).1 = q.1 := by
      have hsb : Int.sign (P.vert (j + 1) - q).1 = 0 := by omega
      have := Int.sign_eq_zero_iff_zero.mp hsb; simp only [Prod.fst_sub] at this; omega
    have ej2 : (P.vert (j + 2)).1 = q.1 := by
      have := Int.sign_eq_zero_iff_zero.mp h2; simp only [Prod.fst_sub] at this; omega
    simp only [crossZ, Prod.fst_sub, Prod.snd_sub, ej, ej1, ej2]; ring
  rcases sign_trichotomy (P.vert j - q).1 with sa | sa | sa
  · have hsb : Int.sign (P.vert (j + 1) - q).1 = 1 := by omega
    rcases sign_trichotomy (P.vert (j + 2) - q).1 with sc | sc | sc <;> rw [sa, hsb, sc] <;> decide
  · have hsb : Int.sign (P.vert (j + 1) - q).1 = 0 := by omega
    have hsc := hnd sa
    rcases sign_trichotomy (P.vert (j + 2) - q).1 with sc | sc | sc
    · rw [sa, hsb, sc]; decide
    · exact absurd sc hsc
    · rw [sa, hsb, sc]; decide
  · have hsb : Int.sign (P.vert (j + 1) - q).1 = -1 := by omega
    rcases sign_trichotomy (P.vert (j + 2) - q).1 with sc | sc | sc <;> rw [sa, hsb, sc] <;> decide

/-- **Unified boundary value.** A point on edge `j`'s line, seeing the other two edges
CCW, with the adjacent column-crossings totalling `2`, has `angleWeight = ½`. Edge `j`
contributes `0` (its cross is zero); the two CCW neighbours contribute `¼` each. This
covers both non-vertical edges (`|sign diff_j| = 2`) and vertical edges uniformly. -/
lemma angleWeight_boundary_eq_half (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (j : ZMod P.n)
    (hj : crossZ (P.vert j - q) (P.vert (j + 1) - q) = 0)
    (h1 : 0 < crossZ (P.vert (j + 1) - q) (P.vert (j + 2) - q))
    (h2 : 0 < crossZ (P.vert (j + 2) - q) (P.vert j - q))
    (hsum : |Int.sign (P.vert (j + 1) - q).1 - Int.sign (P.vert (j + 2) - q).1|
          + |Int.sign (P.vert (j + 2) - q).1 - Int.sign (P.vert j - q).1| = 2) :
    angleWeight P q = 1 / 2 := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn j
  have hgj : (Int.sign (crossZ (P.vert j - q) (P.vert (j + 1) - q)) : ℚ) = 0 := by rw [hj]; simp
  have hgj1 : (Int.sign (crossZ (P.vert (j + 1) - q) (P.vert ((j + 1) + 1) - q)) : ℚ) = 1 := by
    rw [ek12, Int.sign_eq_one_of_pos h1]; norm_num
  have hgj2 : (Int.sign (crossZ (P.vert (j + 2) - q) (P.vert ((j + 2) + 1) - q)) : ℚ) = 1 := by
    rw [ek, Int.sign_eq_one_of_pos h2]; norm_num
  rw [angleWeight_eq_sum, sum_zmodPn_shift P hn j, hgj, hgj1, hgj2, ek12, ek,
    zero_mul, one_mul, one_mul, zero_add]
  have hc : (|Int.sign (P.vert (j + 1) - q).1 - Int.sign (P.vert (j + 2) - q).1| : ℚ)
      + (|Int.sign (P.vert (j + 2) - q).1 - Int.sign (P.vert j - q).1| : ℚ) = 2 := by
    exact_mod_cast hsum
  linarith [hc]

/-- **Exterior, one-negative, unified.** On the wrong side of edge `k` (others CCW), if the
third vertex's x-sign lies *between* edge `k`'s endpoint x-signs (`|d_{k+1}|+|d_{k+2}| =
|d_k|`), then `angleWeight = 0`. No straddle hypothesis — covers straddled, on-column, and
non-straddled exterior uniformly. -/
lemma angleWeight_eq_zero_of_neg_edge_between (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (k : ZMod P.n) (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0)
    (h1 : 0 < crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
    (h2 : 0 < crossZ (P.vert (k + 2) - q) (P.vert k - q))
    (hbtw : |Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1|
          + |Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1|
          = |Int.sign (P.vert k - q).1 - Int.sign (P.vert (k + 1) - q).1|) :
    angleWeight P q = 0 := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  have hgk : (Int.sign (crossZ (P.vert k - q) (P.vert (k + 1) - q)) : ℚ) = -1 := by
    rw [Int.sign_eq_neg_one_of_neg hk]; norm_num
  have hg1 : (Int.sign (crossZ (P.vert (k + 1) - q) (P.vert ((k + 1) + 1) - q)) : ℚ) = 1 := by
    rw [ek12, Int.sign_eq_one_of_pos h1]; norm_num
  have hg2 : (Int.sign (crossZ (P.vert (k + 2) - q) (P.vert ((k + 2) + 1) - q)) : ℚ) = 1 := by
    rw [ek, Int.sign_eq_one_of_pos h2]; norm_num
  rw [angleWeight_eq_sum, sum_zmodPn_shift P hn k, hgk, hg1, hg2, ek12, ek]
  have hc : (|Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1| : ℚ)
      + (|Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1| : ℚ)
      = (|Int.sign (P.vert k - q).1 - Int.sign (P.vert (k + 1) - q).1| : ℚ) := by
    exact_mod_cast hbtw
  linarith [hc]

/-- **Exterior, one-negative (unconditional).** Wrong side of exactly edge `k`, others
CCW ⟹ `angleWeight = 0`. No straddle/column hypotheses — the betweenness is automatic. -/
lemma angleWeight_eq_zero_of_neg_edge (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) < 0)
    (h1 : 0 < crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
    (h2 : 0 < crossZ (P.vert (k + 2) - q) (P.vert k - q)) :
    angleWeight P q = 0 :=
  angleWeight_eq_zero_of_neg_edge_between P hn q k hk h1 h2
    (hbtw_of_neg_edge q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2)) hk h1 h2)

/-- **Exterior, two-negative, unified (given betweenness).** Lone CCW edge `k`, others
wrong-side, betweenness ⟹ `angleWeight = 0`. -/
lemma angleWeight_eq_zero_of_pos_edge_between (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (k : ZMod P.n) (hk : 0 < crossZ (P.vert k - q) (P.vert (k + 1) - q))
    (h1 : crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q) < 0)
    (h2 : crossZ (P.vert (k + 2) - q) (P.vert k - q) < 0)
    (hbtw : |Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1|
          + |Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1|
          = |Int.sign (P.vert k - q).1 - Int.sign (P.vert (k + 1) - q).1|) :
    angleWeight P q = 0 := by
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  have hgk : (Int.sign (crossZ (P.vert k - q) (P.vert (k + 1) - q)) : ℚ) = 1 := by
    rw [Int.sign_eq_one_of_pos hk]; norm_num
  have hg1 : (Int.sign (crossZ (P.vert (k + 1) - q) (P.vert ((k + 1) + 1) - q)) : ℚ) = -1 := by
    rw [ek12, Int.sign_eq_neg_one_of_neg h1]; norm_num
  have hg2 : (Int.sign (crossZ (P.vert (k + 2) - q) (P.vert ((k + 2) + 1) - q)) : ℚ) = -1 := by
    rw [ek, Int.sign_eq_neg_one_of_neg h2]; norm_num
  rw [angleWeight_eq_sum, sum_zmodPn_shift P hn k, hgk, hg1, hg2, ek12, ek]
  have hc : (|Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1| : ℚ)
      + (|Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1| : ℚ)
      = (|Int.sign (P.vert k - q).1 - Int.sign (P.vert (k + 1) - q).1| : ℚ) := by
    exact_mod_cast hbtw
  linarith [hc]

/-- **Exterior, two-negative (unconditional).** Lone CCW edge `k`, others wrong-side ⟹
`angleWeight = 0`. -/
lemma angleWeight_eq_zero_of_two_neg' (P : LatticePolygon) (hn : P.n = 3) (q : Pt) (k : ZMod P.n)
    (hk : 0 < crossZ (P.vert k - q) (P.vert (k + 1) - q))
    (h1 : crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q) < 0)
    (h2 : crossZ (P.vert (k + 2) - q) (P.vert k - q) < 0) :
    angleWeight P q = 0 :=
  angleWeight_eq_zero_of_pos_edge_between P hn q k hk h1 h2
    (hbtw_of_pos_edge q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2)) hk h1 h2)

/-- **On-line exterior, `{0,+,−}`.** `q` on edge `k`'s line off the segment (edge `k+1` CCW,
edge `k+2` wrong-side): the offset barycentric forces edge `k`'s endpoints to share an
x-sign, so the two non-`k` column-weights are equal and `angleWeight = 0`. -/
lemma angleWeight_eq_zero_of_zero_pos_neg (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (k : ZMod P.n) (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : 0 < crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
    (h2 : crossZ (P.vert (k + 2) - q) (P.vert k - q) < 0) :
    angleWeight P q = 0 := by
  have hss : Int.sign (P.vert k - q).1 = Int.sign (P.vert (k + 1) - q).1 := by
    have hoff := barycentric_offset_x q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2))
    rw [hk] at hoff
    have hmul : (P.vert k - q).1 * crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q)
        = (-crossZ (P.vert (k + 2) - q) (P.vert k - q)) * (P.vert (k + 1) - q).1 := by
      linear_combination hoff
    exact sign_eq_of_mul_eq_mul h1 (by linarith) hmul
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  have hgk : (Int.sign (crossZ (P.vert k - q) (P.vert (k + 1) - q)) : ℚ) = 0 := by rw [hk]; simp
  have hg1 : (Int.sign (crossZ (P.vert (k + 1) - q) (P.vert ((k + 1) + 1) - q)) : ℚ) = 1 := by
    rw [ek12, Int.sign_eq_one_of_pos h1]; norm_num
  have hg2 : (Int.sign (crossZ (P.vert (k + 2) - q) (P.vert ((k + 2) + 1) - q)) : ℚ) = -1 := by
    rw [ek, Int.sign_eq_neg_one_of_neg h2]; norm_num
  rw [angleWeight_eq_sum, sum_zmodPn_shift P hn k, hgk, hg1, hg2, ek12, ek]
  have hcc : |Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1|
      = |Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1| := by
    rw [hss]; exact abs_sub_comm _ _
  have hc : (|Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1| : ℚ)
      = (|Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1| : ℚ) := by exact_mod_cast hcc
  linarith [hc]

/-- **On-line exterior, `{0,−,+}`.** Symmetric companion of `angleWeight_eq_zero_of_zero_pos_neg`. -/
lemma angleWeight_eq_zero_of_zero_neg_pos (P : LatticePolygon) (hn : P.n = 3) (q : Pt)
    (k : ZMod P.n) (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (h1 : crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q) < 0)
    (h2 : 0 < crossZ (P.vert (k + 2) - q) (P.vert k - q)) :
    angleWeight P q = 0 := by
  have hss : Int.sign (P.vert k - q).1 = Int.sign (P.vert (k + 1) - q).1 := by
    have hoff := barycentric_offset_x q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2))
    rw [hk] at hoff
    have hmul : (P.vert k - q).1 * (-crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q))
        = crossZ (P.vert (k + 2) - q) (P.vert k - q) * (P.vert (k + 1) - q).1 := by
      linear_combination -hoff
    exact sign_eq_of_mul_eq_mul (by linarith) h2 hmul
  obtain ⟨ek, _, _, ek12⟩ := zmodPn_krel P hn k
  have hgk : (Int.sign (crossZ (P.vert k - q) (P.vert (k + 1) - q)) : ℚ) = 0 := by rw [hk]; simp
  have hg1 : (Int.sign (crossZ (P.vert (k + 1) - q) (P.vert ((k + 1) + 1) - q)) : ℚ) = -1 := by
    rw [ek12, Int.sign_eq_neg_one_of_neg h1]; norm_num
  have hg2 : (Int.sign (crossZ (P.vert (k + 2) - q) (P.vert ((k + 2) + 1) - q)) : ℚ) = 1 := by
    rw [ek, Int.sign_eq_one_of_pos h2]; norm_num
  rw [angleWeight_eq_sum, sum_zmodPn_shift P hn k, hgk, hg1, hg2, ek12, ek]
  have hcc : |Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1|
      = |Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1| := by
    rw [hss]; exact abs_sub_comm _ _
  have hc : (|Int.sign (P.vert (k + 1) - q).1 - Int.sign (P.vert (k + 2) - q).1| : ℚ)
      = (|Int.sign (P.vert (k + 2) - q).1 - Int.sign (P.vert k - q).1| : ℚ) := by exact_mod_cast hcc
  linarith [hc]

/-- **Boundary classification (triangle).** An edge-interior lattice point — on edge `j`,
distinct from both endpoints — has `angleWeight = ½`. Combines `crossZ_j = 0`
(on-segment), both adjacent edges CCW, and the column-sum `= 2`. -/
lemma angleWeight_edge_interior_eq_half (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (j : ZMod P.n)
    (hmem : toReal q ∈ P.edgeSeg j) (hne0 : q ≠ P.vert j) (hne1 : q ≠ P.vert (j + 1)) :
    angleWeight P q = 1 / 2 :=
  angleWeight_boundary_eq_half P hn q j
    (crossZ_eq_zero_of_mem_edgeSeg P q j hmem)
    (crossZ_next_pos_of_mem_edgeSeg P hn horient q j hmem hne1)
    (crossZ_prev_pos_of_mem_edgeSeg P hn horient q j hmem hne0)
    (hsum_of_mem_edgeSeg P hn horient q j hmem hne0 hne1)

/-- The vertices of a simple triangle are distinct (`P.vert` is injective). -/
lemma vert_injective_of_simple (P : LatticePolygon) (hn : P.n = 3) (hsimple : P.IsSimple) :
    Function.Injective P.vert := by
  intro i j hij
  by_contra hne
  rcases zmodPn_ne_cases P hn i j hne with h | h
  · subst h; exact hsimple.1 j hij.symm
  · subst h
    have hk := hsimple.1 (j + 2)
    obtain ⟨ek, _, _, _⟩ := zmodPn_krel P hn j
    rw [ek] at hk
    exact hk hij

/-- A boundary lattice point that is not a vertex lies in some edge's interior, so its
`angleWeight = ½`. -/
lemma angleWeight_half_of_boundary_not_vertex (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hb : q ∈ P.boundaryLattice)
    (hv : ∀ i, q ≠ P.vert i) : angleWeight P q = 1 / 2 := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
  exact angleWeight_edge_interior_eq_half P hn horient q j hj (hv j) (hv (j + 1))

/-- Two adjacent edges on `q`'s lines (`crossZ_k = crossZ_{k+1} = 0`) ⟹ `q` is the shared
vertex `v_{k+1}`, hence on the boundary. -/
lemma mem_boundary_of_adjacent_zero (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (k : ZMod P.n)
    (hk : crossZ (P.vert k - q) (P.vert (k + 1) - q) = 0)
    (hk1 : crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q) = 0) : toReal q ∈ P.boundary := by
  have hq : q = P.vert (k + 1) :=
    eq_vertex_of_adjacent_crossZ_zero q (P.vert k) (P.vert (k + 1)) (P.vert (k + 2)) hk hk1
      (corner_crossZ_ne P hn horient k)
  rw [hq]
  exact vert_mem_boundaryLattice P (k + 1)

/-- **Off-line interior characterization.** Among points off every edge line, the
interior lattice points are exactly those seeing all edges CCW. -/
lemma mem_interiorLattice_iff_of_crossZ_ne (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt)
    (hne : ∀ j, crossZ (P.vert j - q) (P.vert (j + 1) - q) ≠ 0) :
    q ∈ P.interiorLattice ↔ ∀ j, 0 < crossZ (P.vert j - q) (P.vert (j + 1) - q) :=
  ⟨fun hq => all_crossZ_pos_of_mem_interiorLattice P hn horient q hq hne,
    mem_interiorLattice_of_crossZ_pos P hn q⟩

/-- **Exterior vanishing (unified).** A lattice point that is neither interior nor on the
boundary has `angleWeight = 0`. Working from a non-CCW edge `k` (abstract index, so the
classification lemmas apply at `k` cleanly), the three edge-sign trichotomy dispatches to
the banked cases; `#neg = 2` and on-line-at-a-shifted-edge use the `ZMod 3` shift facts. -/
lemma angleWeight_eq_zero_of_not_mem (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (q : Pt) (hint : q ∉ P.interiorLattice)
    (hbdry : toReal q ∉ P.boundary) : angleWeight P q = 0 := by
  obtain ⟨k, hknp⟩ := exists_crossZ_nonpos_of_not_mem P hn horient q hint
  obtain ⟨e21, _, _, e11⟩ := zmodPn_krel P hn k
  obtain ⟨e12, e22⟩ := zmodPn_krel3 P hn k
  have hsum := sum_crossZ_pos P horient q
  rw [sum_zmodPn_shift P hn k, e11, e21] at hsum
  rcases lt_trichotomy (crossZ (P.vert (k + 1) - q) (P.vert (k + 2) - q)) 0 with hb | hb | hb <;>
    rcases lt_trichotomy (crossZ (P.vert (k + 2) - q) (P.vert k - q)) 0 with hc | hc | hc <;>
    rcases lt_trichotomy (crossZ (P.vert k - q) (P.vert (k + 1) - q)) 0 with ha | ha | ha <;>
    first
      | (exfalso; linarith [hknp])
      | (exfalso; linarith [hsum])
      | exact angleWeight_eq_zero_of_neg_edge P hn q k ha hb hc
      | exact angleWeight_eq_zero_of_zero_pos_neg P hn q k ha hb hc
      | exact angleWeight_eq_zero_of_zero_neg_pos P hn q k ha hb hc
      | (exfalso; exact not_crossZ_zero_others_pos P q k hbdry ha hb hc)
      | exact absurd (mem_boundary_of_adjacent_zero P hn horient q k ha hb) hbdry
      | exact angleWeight_eq_zero_of_two_neg' P hn q (k + 1)
          (by rw [e11]; exact hb) (by rw [e11, e12]; exact hc) (by rw [e12]; exact ha)
      | exact angleWeight_eq_zero_of_two_neg' P hn q (k + 2)
          (by rw [e21]; exact hc) (by rw [e21, e22]; exact ha) (by rw [e22]; exact hb)
      | exact angleWeight_eq_zero_of_zero_pos_neg P hn q (k + 1)
          (by rw [e11]; exact hb) (by rw [e11, e12]; exact hc) (by rw [e12]; exact ha)
      | exact angleWeight_eq_zero_of_zero_neg_pos P hn q (k + 1)
          (by rw [e11]; exact hb) (by rw [e11, e12]; exact hc) (by rw [e12]; exact ha)
      | exact angleWeight_eq_zero_of_zero_pos_neg P hn q (k + 2)
          (by rw [e21]; exact hc) (by rw [e21, e22]; exact ha) (by rw [e22]; exact hb)
      | exact angleWeight_eq_zero_of_zero_neg_pos P hn q (k + 2)
          (by rw [e21]; exact hc) (by rw [e21, e22]; exact ha) (by rw [e22]; exact hb)
      | exact absurd (mem_boundary_of_adjacent_zero P hn horient q (k + 1)
          (by rw [e11]; exact hb) (by rw [e11, e12]; exact hc)) hbdry
      | exact absurd (mem_boundary_of_adjacent_zero P hn horient q (k + 2)
          (by rw [e21]; exact hc) (by rw [e21, e22]; exact ha)) hbdry

/-- **Interior sum.** The lattice-angle weights over the interior lattice points total `I`
(each contributes `1`). -/
lemma sum_interiorLattice_angleWeight (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) :
    ∑ q ∈ (interiorLattice_finite P).toFinset, angleWeight P q = (P.I : ℚ) := by
  have hcard : (interiorLattice_finite P).toFinset.card = P.I :=
    (Set.ncard_eq_toFinset_card P.interiorLattice (interiorLattice_finite P)).symm
  rw [Finset.sum_congr rfl fun q hq =>
    angleWeight_eq_one_of_mem_interiorLattice P hn horient q
      ((interiorLattice_finite P).mem_toFinset.mp hq)]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]

/-- The signed column-crossings telescope to `0` around the closed polygon: each edge
contributes `sign((vₖ₊₁−q).1) − sign((vₖ−q).1)`, summing to `0`. (The per-point
`angleWeight` sum uses this to pair `+½` and `−½` column crossings.) -/
lemma sum_sign_x_diff_zero (P : LatticePolygon) (q : Pt) :
    (∑ k, (Int.sign ((P.vert (k + 1) - q).1) - Int.sign ((P.vert k - q).1))) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod P.n))
    (fun k => Int.sign ((P.vert (k + 1) - q).1)) (fun k => Int.sign ((P.vert k - q).1)) (fun _ => rfl)

/-- A finite zero-sum of integers with a nonzero term has both a strictly positive and
a strictly negative term. (Applied to the `dₖ`: gives a `+1` and a `−1` sign.) -/
lemma exists_pos_neg_of_sum_zero {α : Type*} [Fintype α] (f : α → ℤ)
    (hsum : ∑ i, f i = 0) (i₀ : α) (hi : f i₀ ≠ 0) :
    (∃ j, 0 < f j) ∧ (∃ j, f j < 0) := by
  refine ⟨?_, ?_⟩
  · by_contra h; push_neg at h
    refine hi ?_
    have hneg : (∑ i, -f i) = 0 := by rw [Finset.sum_neg_distrib, hsum]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => neg_nonneg.mpr (h j))).mp hneg i₀
      (Finset.mem_univ i₀)
    omega
  · by_contra h; push_neg at h
    exact hi ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h j)).mp hsum i₀ (Finset.mem_univ i₀))

/-- Some x-difference is nonzero: otherwise all vertices share an x-coordinate
(vertical), making the corner cross `0` and contradicting `crossZ_vertex_pos`. -/
lemma exists_x_diff_ne (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented) :
    ∃ k, (P.vert (k + 1)).1 - (P.vert k).1 ≠ 0 := by
  by_contra h; push_neg at h
  have hc := crossZ_vertex_pos P hn horient 0
  rw [crossZ] at hc
  simp only [Prod.fst_sub, Prod.snd_sub] at hc
  have e1 : (P.vert (0 + 1)).1 - (P.vert 0).1 = 0 := h 0
  have e2 : (P.vert (0 - 1)).1 - (P.vert 0).1 = 0 := by
    have h' := h (0 - 1); rw [sub_add_cancel] at h'; omega
  rw [e1, e2] at hc
  simp at hc

/-- Some x-difference has sign `+1` and some has sign `−1` (the two turning extremes),
supplying the `∃±` hypotheses of `sign_abs_sum`. -/
lemma hopf_sign_exists (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented) :
    (∃ k, ((P.vert (k + 1)).1 - (P.vert k).1).sign = 1) ∧
    (∃ k, ((P.vert (k + 1)).1 - (P.vert k).1).sign = -1) := by
  obtain ⟨k₀, hk₀⟩ := exists_x_diff_ne P hn horient
  obtain ⟨⟨jp, hjp⟩, ⟨jn, hjn⟩⟩ := exists_pos_neg_of_sum_zero
    (fun k => (P.vert (k + 1)).1 - (P.vert k).1) (sum_x_diff_zero P) k₀ hk₀
  exact ⟨⟨jp, Int.sign_eq_one_of_pos hjp⟩, ⟨jn, Int.sign_eq_neg_one_of_neg hjn⟩⟩

/-- **Hopf vertex-sum.** For a simple, positively-oriented triangle the three vertex
angle-weights sum to `½ = n/2 − 1`. (The vertices are the boundary lattice points
whose angle-weights carry the `−1` of Pick's formula.) -/
lemma hopf_vertex_sum (P : LatticePolygon) (hn : P.n = 3) (horient : P.PositivelyOriented) :
    (∑ k, angleWeight P (P.vert k)) = 1 / 2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := zmodPn_idx P hn
  obtain ⟨⟨jp, hjp⟩, ⟨jn, hjn⟩⟩ := hopf_sign_exists P hn horient
  have hp : ((P.vert 1).1 - (P.vert 0).1).sign = 1 ∨ ((P.vert 2).1 - (P.vert 1).1).sign = 1
      ∨ ((P.vert 0).1 - (P.vert 2).1).sign = 1 := by
    rcases zmodPn_cases P hn jp with h | h | h
    · subst h; rw [e1] at hjp; exact Or.inl hjp
    · subst h; rw [e2] at hjp; exact Or.inr (Or.inl hjp)
    · subst h; rw [e3] at hjp; exact Or.inr (Or.inr hjp)
  have hm : ((P.vert 1).1 - (P.vert 0).1).sign = -1 ∨ ((P.vert 2).1 - (P.vert 1).1).sign = -1
      ∨ ((P.vert 0).1 - (P.vert 2).1).sign = -1 := by
    rcases zmodPn_cases P hn jn with h | h | h
    · subst h; rw [e1] at hjn; exact Or.inl hjn
    · subst h; rw [e2] at hjn; exact Or.inr (Or.inl hjn)
    · subst h; rw [e3] at hjn; exact Or.inr (Or.inr hjn)
  have hsum := sign_abs_sum _ _ _ (sign_trichotomy ((P.vert 1).1 - (P.vert 0).1))
    (sign_trichotomy ((P.vert 2).1 - (P.vert 1).1))
    (sign_trichotomy ((P.vert 0).1 - (P.vert 2).1)) hp hm
  have hS : |((P.vert 1).1 - (P.vert 0).1).sign + ((P.vert 0).1 - (P.vert 2).1).sign|
      + |((P.vert 2).1 - (P.vert 1).1).sign + ((P.vert 1).1 - (P.vert 0).1).sign|
      + |((P.vert 0).1 - (P.vert 2).1).sign + ((P.vert 2).1 - (P.vert 1).1).sign| = 2 := by
    rw [add_comm (((P.vert 2).1 - (P.vert 1).1).sign) (((P.vert 1).1 - (P.vert 0).1).sign),
      add_comm (((P.vert 0).1 - (P.vert 2).1).sign) (((P.vert 2).1 - (P.vert 1).1).sign)]
    exact hsum
  have hcast : ∀ x y : ℤ, |(↑x : ℚ) + ↑y| = (↑|x + y| : ℚ) := by
    intro x y; rw [← Int.cast_add, Int.cast_abs]
  rw [sum_zmodPn P hn (fun k => angleWeight P (P.vert k)),
    angleWeight_vertex_g P hn horient 0, angleWeight_vertex_g P hn horient 1,
    angleWeight_vertex_g P hn horient 2, e1, e2, e3, e4, e5, e6,
    hcast, hcast, hcast, ← add_div, ← add_div, ← Int.cast_add, ← Int.cast_add, hS]
  norm_num

/-- **Vertex sum.** The lattice-angle weights over the three (distinct) vertices total `½`
— the Hopf turning content (the source of the `−1`). -/
lemma sum_vertices_angleWeight (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (hsimple : P.IsSimple) :
    ∑ q ∈ Finset.univ.image P.vert, angleWeight P q = 1 / 2 := by
  rw [Finset.sum_image (fun i _ j _ h => vert_injective_of_simple P hn hsimple h)]
  exact hopf_vertex_sum P hn horient

/-- **Boundary sum.** The lattice-angle weights over the boundary lattice points total
`B/2 − 1`: the three vertices contribute `½` (Hopf), and the remaining `B − 3` edge-interior
points contribute `½` each. -/
lemma sum_boundaryLattice_angleWeight (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (hsimple : P.IsSimple) :
    ∑ q ∈ (boundaryLattice_finite P).toFinset, angleWeight P q = (P.B : ℚ) / 2 - 1 := by
  set bdry := (boundaryLattice_finite P).toFinset with hbdry
  set V := Finset.univ.image P.vert with hV
  have hVsub : V ⊆ bdry := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
    exact (Set.Finite.mem_toFinset _).2 (vert_mem_boundaryLattice P i)
  have hVcard : V.card = 3 := by
    rw [hV, Finset.card_image_of_injective _ (vert_injective_of_simple P hn hsimple),
      Finset.card_univ, ZMod.card, hn]
  have hBcard : bdry.card = P.B :=
    (Set.ncard_eq_toFinset_card P.boundaryLattice (boundaryLattice_finite P)).symm
  have hge : 3 ≤ P.B := by rw [← hVcard, ← hBcard]; exact Finset.card_le_card hVsub
  have hD : ∑ q ∈ bdry \ V, angleWeight P q = (1 / 2 : ℚ) * ((bdry \ V).card : ℚ) := by
    rw [Finset.sum_congr rfl fun q hq => angleWeight_half_of_boundary_not_vertex P hn horient q
      ((Set.Finite.mem_toFinset _).1 (Finset.mem_sdiff.1 hq).1)
      (fun i hqi => (Finset.mem_sdiff.1 hq).2 (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hqi.symm⟩)),
      Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsumV : ∑ q ∈ V, angleWeight P q = 1 / 2 := by
    rw [hV]; exact sum_vertices_angleWeight P hn horient hsimple
  have hcardNat : (bdry \ V).card = P.B - 3 := by
    have h := Finset.card_sdiff_add_card_eq_card hVsub
    rw [hVcard, hBcard] at h
    omega
  have hcard : ((bdry \ V).card : ℚ) = (P.B : ℚ) - 3 := by
    rw [hcardNat, Nat.cast_sub hge]; push_cast; ring
  rw [← Finset.sum_sdiff hVsub, hsumV, hD, hcard]
  ring

/-- **The count identity (triangle).** `∑ᶠ angleWeight = I + B/2 − 1`: the box sum splits
(support ⊆ interior ∪ boundary, disjoint) into the interior sum `I` and the boundary sum
`B/2 − 1`. -/
lemma finsum_angleWeight_eq (P : LatticePolygon) (hn : P.n = 3)
    (horient : P.PositivelyOriented) (hsimple : P.IsSimple) :
    (∑ᶠ q, angleWeight P q) = (P.I : ℚ) + (P.B : ℚ) / 2 - 1 := by
  have hsupp : Function.support (fun q => angleWeight P q) ⊆
      ↑((interiorLattice_finite P).toFinset ∪ (boundaryLattice_finite P).toFinset) := by
    intro q hq
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    by_contra h
    push_neg at h
    exact hq (angleWeight_eq_zero_of_not_mem P hn horient q h.1 h.2)
  have hdisj : Disjoint (interiorLattice_finite P).toFinset (boundaryLattice_finite P).toFinset := by
    rw [Finset.disjoint_left]
    intro q hqi hqb
    exact Set.disjoint_left.1 (interiorLattice_disjoint_boundaryLattice P)
      ((Set.Finite.mem_toFinset _).1 hqi) ((Set.Finite.mem_toFinset _).1 hqb)
  rw [finsum_eq_finset_sum_of_support_subset _ hsupp, Finset.sum_union hdisj,
    sum_interiorLattice_angleWeight P hn horient,
    sum_boundaryLattice_angleWeight P hn horient hsimple]
  ring

/-- **Pick's theorem for triangles** (`n = 3`), sorry-free: discharges the `hcount`
hypothesis of `pick_triangle` with the count identity `∑ᶠ angleWeight = I + B/2 − 1`. -/
theorem pick_n3 (P : LatticePolygon) (hn : P.n = 3) (hsimple : P.IsSimple)
    (horient : P.PositivelyOriented) : P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_triangle P hsimple hn horient (by
    rw [finsum_angleWeight_eq P hn horient hsimple]; push_cast; ring)

/-- A simple polygon has at least three vertices (degenerate `n = 1, 2` are excluded by
`IsSimple`). A step toward the general-`n` case split. -/
lemma simple_imp_three_le_n (P : LatticePolygon) (hsimple : P.IsSimple) : 3 ≤ P.n := by
  rcases P with ⟨n, pos, vert⟩
  by_contra hlt
  push_neg at hlt
  interval_cases n
  · exact hsimple.1 0 rfl
  · have hd := hsimple.2.2 0
    have hv0 : toReal (vert 0) ∈ (⟨2, pos, vert⟩ : LatticePolygon).edgeSeg 0 ∩
        (⟨2, pos, vert⟩ : LatticePolygon).edgeSeg (0 + 1) :=
      ⟨left_mem_segment ℝ _ _, by
        show toReal (vert 0) ∈ segment ℝ (toReal (vert (0 + 1))) (toReal (vert (0 + 1 + 1)))
        rw [show (0 + 1 + 1 : ZMod 2) = 0 from by decide]
        exact right_mem_segment ℝ _ _⟩
    rw [hd, Set.mem_singleton_iff] at hv0
    exact hsimple.1 0 (toReal_injective hv0)

/-- **Reversed-edge cancellation.** Traversing an edge in the opposite direction negates
its winding contribution, so `edgeWind a b q + edgeWind b a q = 0`. This is the per-edge
basis of winding additivity across a shared diagonal (the foundation for the general-`n`
ear-clipping area additivity). -/
lemma edgeWind_antisymm (a b q : ℝ × ℝ) :
    LatticePolygon.edgeWind a b q + LatticePolygon.edgeWind b a q = 0 := by
  have hc : cross (a - b) (q - b) = - cross (b - a) (q - a) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  simp only [LatticePolygon.edgeWind, hc]
  split_ifs <;> first | omega | (exfalso; simp_all <;> linarith)

/-- A degenerate edge (both endpoints equal) contributes nothing to the winding. -/
lemma edgeWind_self (a q : ℝ × ℝ) : LatticePolygon.edgeWind a a q = 0 := by
  unfold LatticePolygon.edgeWind
  split_ifs with h1 h2
  · exact absurd h1.2.1 (not_lt.2 h1.1)
  · exact absurd h2.2.1 (not_lt.2 h2.1)
  · rfl

/-- **Rotation invariance of winding.** Cyclically relabeling the vertices (start at `+c`)
leaves the winding unchanged — the sum over `ZMod n` is shift-invariant. Lets ear-clipping
place the ear at vertex `0` without loss of generality. -/
lemma winding_rotate (P : LatticePolygon) (c : ZMod P.n) (q : ℝ × ℝ) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).winding q = P.winding q := by
  rw [LatticePolygon.winding, LatticePolygon.winding,
    ← Equiv.sum_comp (Equiv.addRight c)
      (fun j => LatticePolygon.edgeWind (toReal (P.vert j)) (toReal (P.vert (j + 1))) q)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.coe_addRight]
  rw [show (i + 1 + c : ZMod P.n) = i + c + 1 from by ring]

/-- The interior region is rotation-invariant (consequence of `winding_rotate`). -/
lemma interiorRegion_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).interiorRegion = P.interiorRegion := by
  ext q
  simp only [LatticePolygon.interiorRegion, Set.mem_setOf_eq]
  rw [winding_rotate]

/-- The enclosed area is rotation-invariant. -/
lemma area_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).area = P.area := by
  rw [LatticePolygon.area, LatticePolygon.area, interiorRegion_rotate]

/-- Rotated edge `i` is the original edge `i + c`. -/
lemma edgeSeg_rotate (P : LatticePolygon) (c i : ZMod P.n) :
    (⟨P.n, P.pos, fun j => P.vert (j + c)⟩ : LatticePolygon).edgeSeg i = P.edgeSeg (i + c) := by
  simp only [LatticePolygon.edgeSeg]
  rw [show (i + 1 + c : ZMod P.n) = i + c + 1 from by ring]

/-- The boundary curve is rotation-invariant. -/
lemma boundary_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun j => P.vert (j + c)⟩ : LatticePolygon).boundary = P.boundary := by
  simp only [LatticePolygon.boundary, edgeSeg_rotate]
  exact (Equiv.addRight c).iSup_comp (g := fun j => P.edgeSeg j)

/-- The interior lattice set is rotation-invariant. -/
lemma interiorLattice_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).interiorLattice = P.interiorLattice := by
  ext q
  simp only [LatticePolygon.interiorLattice, Set.mem_setOf_eq, winding_rotate, boundary_rotate]

/-- The boundary lattice set is rotation-invariant. -/
lemma boundaryLattice_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).boundaryLattice = P.boundaryLattice := by
  ext q
  simp only [LatticePolygon.boundaryLattice, Set.mem_setOf_eq, boundary_rotate]

/-- `I` is rotation-invariant. -/
lemma I_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).I = P.I := by
  rw [LatticePolygon.I, LatticePolygon.I, interiorLattice_rotate]

/-- `B` is rotation-invariant. -/
lemma B_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).B = P.B := by
  rw [LatticePolygon.B, LatticePolygon.B, boundaryLattice_rotate]

/-- The shoelace (signed area) is rotation-invariant. -/
lemma shoelace_rotate (P : LatticePolygon) (c : ZMod P.n) :
    (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).shoelace = P.shoelace := by
  rw [LatticePolygon.shoelace, LatticePolygon.shoelace]
  congr 1
  rw [← Equiv.sum_comp (Equiv.addRight c)
    (fun j => cross (toReal (P.vert j)) (toReal (P.vert (j + 1))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.coe_addRight]
  rw [show (i + 1 + c : ZMod P.n) = i + c + 1 from by ring]

/-- The `(n−1)`-gon obtained by deleting the last vertex `vₙ₋₁`: vertices `v₀,…,vₙ₋₂` in
order, closing with the diagonal `vₙ₋₂ → v₀`. The first step of the ear-clipping split. -/
def deleteLast (P : LatticePolygon) (h : 2 ≤ P.n) : LatticePolygon where
  n := P.n - 1
  pos := by omega
  vert := fun j => P.vert (j.val : ZMod P.n)

@[simp] lemma deleteLast_n (P : LatticePolygon) (h : 2 ≤ P.n) :
    (deleteLast P h).n = P.n - 1 := rfl

@[simp] lemma deleteLast_vert (P : LatticePolygon) (h : 2 ≤ P.n) (j : ZMod (P.n - 1)) :
    (deleteLast P h).vert j = P.vert (j.val : ZMod P.n) := rfl

/-- **Winding additivity through ear-clipping.** Deleting the last vertex splits the polygon's
winding into the smaller polygon's winding plus the winding of the ear triangle
`(vₘ, vₘ₊₁, v₀)`, using `edgeWind_antisymm` on the shared diagonal `vₘ ↔ v₀`. -/
lemma winding_deleteLast_add_ear (P : LatticePolygon) (h : 2 ≤ P.n) (q : ℝ × ℝ)
    (m : ℕ) (hm : P.n = m + 2) :
    P.winding q
      = (deleteLast P h).winding q
        + LatticePolygon.edgeWind (toReal (P.vert ((m : ZMod P.n))))
            (toReal (P.vert ((m : ZMod P.n) + 1))) q
        + LatticePolygon.edgeWind (toReal (P.vert ((m : ZMod P.n) + 1)))
            (toReal (P.vert 0)) q
        + LatticePolygon.edgeWind (toReal (P.vert 0))
            (toReal (P.vert (m : ZMod P.n))) q := by
  obtain ⟨n, pos, vert⟩ := P
  subst hm
  simp only [LatticePolygon.winding, deleteLast]
  show (∑ x : Fin (m+2), edgeWind (toReal (vert x)) (toReal (vert (x + (1 : Fin (m+2))))) q)
      = (∑ x : Fin (m+1), edgeWind (toReal (vert ↑(Fin.val x))) (toReal (vert ↑(Fin.val (x + (1 : Fin (m+1)))))) q)
        + edgeWind (toReal (vert ↑m)) (toReal (vert (↑m + 1))) q
        + edgeWind (toReal (vert (↑m + 1))) (toReal (vert 0)) q
        + edgeWind (toReal (vert 0)) (toReal (vert ↑m)) q
  rw [Fin.sum_univ_castSucc (n := m + 1), Fin.sum_univ_castSucc (n := m),
    Fin.sum_univ_castSucc (n := m)]
  -- Index identities in `ZMod (m+2) = Fin (m+2)`.
  have e1 : ∀ i : Fin m, (i.castSucc.castSucc : Fin (m+2))
      = (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2)) := by
    intro i
    apply Fin.val_injective
    rw [Fin.val_castSucc, Fin.val_castSucc]
    show i.val = ZMod.val (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by simp [Fin.val_castSucc]; omega)]
    simp [Fin.val_castSucc]
  have e2 : ∀ i : Fin m, (i.castSucc.castSucc + 1 : Fin (m+2))
      = (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)) := by
    intro i
    apply Fin.val_injective
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last]),
      Fin.val_castSucc, Fin.val_castSucc]
    show i.val + 1 = ZMod.val (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by
      rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last])]
      simp [Fin.val_castSucc])]
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last])]
    simp [Fin.val_castSucc]
  have eDiag1 : (((Fin.last m : Fin (m+1)).val : ℕ) : ZMod (m+2)) = (m : ZMod (m+2)) := by
    simp [Fin.val_last]
  have eDiag2 : (((Fin.last m + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)) = (0 : ZMod (m+2)) := by
    rw [show (Fin.last m + 1 : Fin (m+1)) = 0 by
      apply Fin.val_injective; simp [Fin.val_last, Fin.val_add_one]]
    simp
  have eEarA1 : ((Fin.last m).castSucc : Fin (m+2)) = (m : ZMod (m+2)) := by
    apply Fin.val_injective
    rw [Fin.val_castSucc, Fin.val_last]
    show m = ZMod.val ((m : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  have eEarB1 : (Fin.last (m+1) : Fin (m+2)) = ((m : ZMod (m+2)) + 1 : ZMod (m+2)) := by
    have h1 : ((m : ZMod (m+2)) + 1 : ZMod (m+2)) = ((m+1 : ℕ) : ZMod (m+2)) := by push_cast; ring
    rw [h1]
    apply Fin.val_injective
    rw [Fin.val_last]
    show m + 1 = ZMod.val ((m+1 : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  have eEarB2 : (Fin.last (m+1) + 1 : Fin (m+2)) = (0 : ZMod (m+2)) := by
    have h0 : (Fin.last (m+1) + 1 : Fin (m+2)) = (0 : Fin (m+2)) := by
      apply Fin.val_injective; simp [Fin.val_last, Fin.val_add_one]
    exact h0
  have eEarA2 : ((Fin.last m).castSucc + 1 : Fin (m+2)) = ((m : ZMod (m+2)) + 1 : ZMod (m+2)) := by
    have h1 : ((m : ZMod (m+2)) + 1 : ZMod (m+2)) = ((m+1 : ℕ) : ZMod (m+2)) := by push_cast; ring
    rw [h1]
    apply Fin.val_injective
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last]),
      Fin.val_castSucc, Fin.val_last]
    show m + 1 = ZMod.val ((m+1 : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  -- Rewrite every vertex index to its canonical `ZMod (m+2)` form.
  rw [eEarA2, eEarA1, eDiag1, eDiag2, eEarB2, eEarB1]
  -- The subsum bodies match term-by-term.
  have hsub : (∑ i : Fin m, edgeWind (toReal (vert i.castSucc.castSucc))
        (toReal (vert (i.castSucc.castSucc + (1 : Fin (m+2))))) q)
      = ∑ i : Fin m, edgeWind (toReal (vert (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2))))
          (toReal (vert (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)))) q := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, e1]
  rw [hsub]
  -- The diagonal `vₘ → v₀` and its reverse `v₀ → vₘ` cancel.
  have hanti := edgeWind_antisymm (toReal (vert (m : ZMod (m+2)))) (toReal (vert 0)) q
  linarith [hanti]

/-- The cross-sum (shoelace numerator) splits through `deleteLast` the same way as
the winding number: the deleted wrap edge is the diagonal `vₘ → v₀`, which cancels
against the ear's reverse edge `v₀ → vₘ` via `cross_skew`. -/
lemma cross_sum_deleteLast_add_ear (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ)
    (hm : P.n = m + 2) :
    (∑ i, cross (toReal (P.vert i)) (toReal (P.vert (i + 1))))
      = (∑ j, cross (toReal ((deleteLast P h).vert j))
            (toReal ((deleteLast P h).vert (j + 1))))
        + cross (toReal (P.vert (m : ZMod P.n))) (toReal (P.vert ((m : ZMod P.n) + 1)))
        + cross (toReal (P.vert ((m : ZMod P.n) + 1))) (toReal (P.vert 0))
        + cross (toReal (P.vert 0)) (toReal (P.vert (m : ZMod P.n))) := by
  obtain ⟨n, pos, vert⟩ := P
  subst hm
  simp only [deleteLast]
  show (∑ x : Fin (m+2), cross (toReal (vert x)) (toReal (vert (x + (1 : Fin (m+2))))))
      = (∑ x : Fin (m+1), cross (toReal (vert ↑(Fin.val x))) (toReal (vert ↑(Fin.val (x + (1 : Fin (m+1)))))))
        + cross (toReal (vert ↑m)) (toReal (vert (↑m + 1)))
        + cross (toReal (vert (↑m + 1))) (toReal (vert 0))
        + cross (toReal (vert 0)) (toReal (vert ↑m))
  rw [Fin.sum_univ_castSucc (n := m + 1), Fin.sum_univ_castSucc (n := m),
    Fin.sum_univ_castSucc (n := m)]
  -- Index identities in `ZMod (m+2) = Fin (m+2)`.
  have e1 : ∀ i : Fin m, (i.castSucc.castSucc : Fin (m+2))
      = (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2)) := by
    intro i
    apply Fin.val_injective
    rw [Fin.val_castSucc, Fin.val_castSucc]
    show i.val = ZMod.val (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by simp [Fin.val_castSucc]; omega)]
    simp [Fin.val_castSucc]
  have e2 : ∀ i : Fin m, (i.castSucc.castSucc + 1 : Fin (m+2))
      = (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)) := by
    intro i
    apply Fin.val_injective
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last]),
      Fin.val_castSucc, Fin.val_castSucc]
    show i.val + 1 = ZMod.val (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by
      rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last])]
      simp [Fin.val_castSucc])]
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last])]
    simp [Fin.val_castSucc]
  have eDiag1 : (((Fin.last m : Fin (m+1)).val : ℕ) : ZMod (m+2)) = (m : ZMod (m+2)) := by
    simp [Fin.val_last]
  have eDiag2 : (((Fin.last m + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)) = (0 : ZMod (m+2)) := by
    rw [show (Fin.last m + 1 : Fin (m+1)) = 0 by
      apply Fin.val_injective; simp [Fin.val_last, Fin.val_add_one]]
    simp
  have eEarA1 : ((Fin.last m).castSucc : Fin (m+2)) = (m : ZMod (m+2)) := by
    apply Fin.val_injective
    rw [Fin.val_castSucc, Fin.val_last]
    show m = ZMod.val ((m : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  have eEarB1 : (Fin.last (m+1) : Fin (m+2)) = ((m : ZMod (m+2)) + 1 : ZMod (m+2)) := by
    have h1 : ((m : ZMod (m+2)) + 1 : ZMod (m+2)) = ((m+1 : ℕ) : ZMod (m+2)) := by push_cast; ring
    rw [h1]
    apply Fin.val_injective
    rw [Fin.val_last]
    show m + 1 = ZMod.val ((m+1 : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  have eEarB2 : (Fin.last (m+1) + 1 : Fin (m+2)) = (0 : ZMod (m+2)) := by
    have h0 : (Fin.last (m+1) + 1 : Fin (m+2)) = (0 : Fin (m+2)) := by
      apply Fin.val_injective; simp [Fin.val_last, Fin.val_add_one]
    exact h0
  have eEarA2 : ((Fin.last m).castSucc + 1 : Fin (m+2)) = ((m : ZMod (m+2)) + 1 : ZMod (m+2)) := by
    have h1 : ((m : ZMod (m+2)) + 1 : ZMod (m+2)) = ((m+1 : ℕ) : ZMod (m+2)) := by push_cast; ring
    rw [h1]
    apply Fin.val_injective
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last]),
      Fin.val_castSucc, Fin.val_last]
    show m + 1 = ZMod.val ((m+1 : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  -- Rewrite every vertex index to its canonical `ZMod (m+2)` form.
  rw [eEarA2, eEarA1, eDiag1, eDiag2, eEarB2, eEarB1]
  -- The subsum bodies match term-by-term.
  have hsub : (∑ i : Fin m, cross (toReal (vert i.castSucc.castSucc))
        (toReal (vert (i.castSucc.castSucc + (1 : Fin (m+2))))))
      = ∑ i : Fin m, cross (toReal (vert (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2))))
          (toReal (vert (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, e1]
  rw [hsub]
  -- The diagonal `vₘ → v₀` and its reverse `v₀ → vₘ` cancel.
  have hanti := cross_skew (toReal (vert (m : ZMod (m+2)))) (toReal (vert 0))
  linarith [hanti]

/-- Shoelace form of `cross_sum_deleteLast_add_ear`: removing the last vertex drops the
signed area by half the (signed) area of the ear triangle `(vₘ, vₘ₊₁, v₀)`. -/
lemma shoelace_deleteLast_add_ear (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ)
    (hm : P.n = m + 2) :
    P.shoelace = (deleteLast P h).shoelace
      + (cross (toReal (P.vert (m : ZMod P.n))) (toReal (P.vert ((m : ZMod P.n) + 1)))
         + cross (toReal (P.vert ((m : ZMod P.n) + 1))) (toReal (P.vert 0))
         + cross (toReal (P.vert 0)) (toReal (P.vert (m : ZMod P.n)))) / 2 := by
  simp only [LatticePolygon.shoelace, cross_sum_deleteLast_add_ear P h m hm]
  ring

/-- The **ear triangle** `(vₘ, vₘ₊₁, v₀)` of `P` as a standalone 3-vertex polygon. -/
def earTri (P : LatticePolygon) (m : ℕ) (hm : P.n = m + 2) : LatticePolygon where
  n := 3
  pos := by norm_num
  vert := ![P.vert (m : ZMod P.n), P.vert ((m : ZMod P.n) + 1), P.vert 0]

lemma earTri_winding (P : LatticePolygon) (m : ℕ) (hm : P.n = m + 2) (q : ℝ × ℝ) :
    (earTri P m hm).winding q
      = LatticePolygon.edgeWind (toReal (P.vert (m : ZMod P.n))) (toReal (P.vert ((m : ZMod P.n) + 1))) q
        + LatticePolygon.edgeWind (toReal (P.vert ((m : ZMod P.n) + 1))) (toReal (P.vert 0)) q
        + LatticePolygon.edgeWind (toReal (P.vert 0)) (toReal (P.vert (m : ZMod P.n))) q := by
  rw [LatticePolygon.winding]
  exact Fin.sum_univ_three _

lemma earTri_shoelace (P : LatticePolygon) (m : ℕ) (hm : P.n = m + 2) :
    (earTri P m hm).shoelace
      = (cross (toReal (P.vert (m : ZMod P.n))) (toReal (P.vert ((m : ZMod P.n) + 1)))
         + cross (toReal (P.vert ((m : ZMod P.n) + 1))) (toReal (P.vert 0))
         + cross (toReal (P.vert 0)) (toReal (P.vert (m : ZMod P.n)))) / 2 := by
  rw [LatticePolygon.shoelace]
  congr 1
  exact Fin.sum_univ_three _

lemma winding_eq_deleteLast_add_earTri (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ)
    (hm : P.n = m + 2) (q : ℝ × ℝ) :
    P.winding q = (deleteLast P h).winding q + (earTri P m hm).winding q := by
  rw [earTri_winding, winding_deleteLast_add_ear P h q m hm]
  ring

lemma shoelace_eq_deleteLast_add_earTri (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ)
    (hm : P.n = m + 2) :
    P.shoelace = (deleteLast P h).shoelace + (earTri P m hm).shoelace := by
  rw [earTri_shoelace, shoelace_deleteLast_add_ear P h m hm]

/-- **The `h01` (winding ∈ {0,1}) induction step**, given interior non-overlap.
If the sub-polygon `deleteLast P` and the ear triangle each have winding in `{0,1}` a.e.
and their interiors don't overlap (never both winding `1`), then `P` has winding in `{0,1}`
a.e. Uses the winding additivity `winding_P = winding_{deleteLast} + winding_{earTri}`.
The non-overlap hypothesis is exactly the geometric ear-validity fact still to be proven. -/
lemma h01_of_split (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ) (hm : P.n = m + 2)
    (hdL : ∀ᵐ q ∂MeasureTheory.volume,
      (deleteLast P h).winding q = 0 ∨ (deleteLast P h).winding q = 1)
    (hear : ∀ᵐ q ∂MeasureTheory.volume,
      (earTri P m hm).winding q = 0 ∨ (earTri P m hm).winding q = 1)
    (hdisj : ∀ q, ¬((deleteLast P h).winding q = 1 ∧ (earTri P m hm).winding q = 1)) :
    ∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1 := by
  filter_upwards [hdL, hear] with q hq1 hq2
  rw [winding_eq_deleteLast_add_earTri P h m hm q]
  rcases hq1 with h0 | h1 <;> rcases hq2 with h0' | h1'
  · omega
  · omega
  · omega
  · exact absurd ⟨h1, h1'⟩ (hdisj q)

/-- **The Pick-count-identity (`shoelace = I + B/2 − 1`) induction step**, given the
`I`/`B` lattice additivity across the diagonal. The hypothesis `hIB` packages the count
bookkeeping (`I_P + B_P/2 = I_{dL} + I_{ear} + (B_{dL}+B_{ear})/2 − 1`, in which the
diagonal interior-lattice-point count cancels); given it plus the identity for the two
pieces, it holds for `P`. Combined with `shoelace_eq_deleteLast_add_earTri`. -/
lemma PCI_of_split (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ) (hm : P.n = m + 2)
    (hdL : (deleteLast P h).shoelace
      = ((deleteLast P h).I : ℝ) + ((deleteLast P h).B : ℝ) / 2 - 1)
    (hear : (earTri P m hm).shoelace
      = ((earTri P m hm).I : ℝ) + ((earTri P m hm).B : ℝ) / 2 - 1)
    (hIB : (P.I : ℝ) + (P.B : ℝ) / 2
      = ((deleteLast P h).I : ℝ) + ((earTri P m hm).I : ℝ)
        + (((deleteLast P h).B : ℝ) + ((earTri P m hm).B : ℝ)) / 2 - 1) :
    P.shoelace = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 := by
  rw [shoelace_eq_deleteLast_add_earTri P h m hm, hdL, hear]
  linarith [hIB]

/-- **The Pick count identity for triangles** (`shoelace = I + B/2 − 1`): the base case of
the count-identity induction, and the input for the ear triangle. From `shoelace = ∑ᶠ
angleWeight` (Step 1) and the triangle count `finsum_angleWeight_eq`. -/
lemma PCI_triangle (T : LatticePolygon) (hn : T.n = 3) (hsimple : T.IsSimple)
    (horient : T.PositivelyOriented) :
    T.shoelace = (T.I : ℝ) + (T.B : ℝ) / 2 - 1 := by
  rw [shoelace_eq_finsum, finsum_angleWeight_eq T hn horient hsimple]
  push_cast
  ring

/-- **Boundary (edge-set) additivity through ear-clipping.** The union of the smaller
polygon's boundary and the ear triangle's boundary equals `P`'s boundary together with the
diagonal segment `vₘ → v₀`. The set analogue of `winding_deleteLast_add_ear`. -/
lemma boundary_deleteLast_union_earTri (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ)
    (hm : P.n = m + 2) :
    (deleteLast P h).boundary ∪ (earTri P m hm).boundary
      = P.boundary ∪ segment ℝ (toReal (P.vert (m : ZMod P.n))) (toReal (P.vert 0)) := by
  have hearB : (earTri P m hm).boundary
      = segment ℝ (toReal (P.vert (m : ZMod P.n))) (toReal (P.vert ((m : ZMod P.n) + 1)))
        ∪ segment ℝ (toReal (P.vert ((m : ZMod P.n) + 1))) (toReal (P.vert 0))
        ∪ segment ℝ (toReal (P.vert 0)) (toReal (P.vert (m : ZMod P.n))) := by
    rw [LatticePolygon.boundary]
    apply Set.Subset.antisymm
    · apply Set.iUnion_subset
      intro i
      rcases zmod3_cases i with rfl | rfl | rfl <;>
        simp only [LatticePolygon.edgeSeg, earTri, show ((1:ZMod 3)+1 = 2) from rfl,
          show ((2:ZMod 3)+1 = 0) from rfl, show ((0:ZMod 3)+1 = 1) from rfl,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] <;> intro y hy
      · exact Or.inl (Or.inl hy)
      · exact Or.inl (Or.inr hy)
      · exact Or.inr hy
    · intro y hy
      rcases hy with (hy | hy) | hy
      · refine Set.mem_iUnion.2 ⟨0, ?_⟩
        simp only [LatticePolygon.edgeSeg, earTri, show ((0:ZMod 3)+1 = 1) from rfl,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact hy
      · refine Set.mem_iUnion.2 ⟨1, ?_⟩
        simp only [LatticePolygon.edgeSeg, earTri, show ((1:ZMod 3)+1 = 2) from rfl,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        exact hy
      · refine Set.mem_iUnion.2 ⟨2, ?_⟩
        simp only [LatticePolygon.edgeSeg, earTri, show ((2:ZMod 3)+1 = 0) from rfl,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero]
        exact hy
  rw [hearB]; clear hearB
  obtain ⟨n, pos, vert⟩ := P
  subst hm
  simp only [LatticePolygon.boundary, LatticePolygon.edgeSeg, deleteLast]
  show ((⋃ i : Fin (m+1), segment ℝ (toReal (vert ((i.val : ℕ) : ZMod (m+2))))
        (toReal (vert (((i + (1:Fin (m+1))).val : ℕ) : ZMod (m+2))))) ∪ _)
      = ((⋃ i : Fin (m+2), segment ℝ (toReal (vert i)) (toReal (vert (i + (1:Fin (m+2)))))) ∪ _)
  rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc (n := m+1)
        (f := fun i : Fin (m+2) => segment ℝ (toReal (vert i)) (toReal (vert (i + (1:Fin (m+2)))))),
      Set.iUnion_fin_add_one_eq_iUnion_castSucc (n := m)
        (f := fun i : Fin (m+1) => segment ℝ (toReal (vert ((i.val : ℕ) : ZMod (m+2))))
          (toReal (vert (((i + (1:Fin (m+1))).val : ℕ) : ZMod (m+2))))),
      Set.iUnion_fin_add_one_eq_iUnion_castSucc (n := m)
        (f := (fun i : Fin (m+2) => segment ℝ (toReal (vert i)) (toReal (vert (i + (1:Fin (m+2)))))) ∘ Fin.castSucc)]
  -- Index identities (mirroring `winding_deleteLast_add_ear`).
  have e1 : ∀ i : Fin m, (i.castSucc.castSucc : Fin (m+2))
      = (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2)) := by
    intro i
    apply Fin.val_injective
    rw [Fin.val_castSucc, Fin.val_castSucc]
    show i.val = ZMod.val (((i.castSucc : Fin (m+1)).val : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by simp [Fin.val_castSucc]; omega)]
    simp [Fin.val_castSucc]
  have e2 : ∀ i : Fin m, (i.castSucc.castSucc + 1 : Fin (m+2))
      = (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)) := by
    intro i
    apply Fin.val_injective
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last]),
      Fin.val_castSucc, Fin.val_castSucc]
    show i.val + 1 = ZMod.val (((i.castSucc + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by
      rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last])]
      simp [Fin.val_castSucc])]
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last])]
    simp [Fin.val_castSucc]
  -- The two `Fin m` subunions agree term-by-term.
  have hsub : (Set.iUnion ((fun i : Fin (m+1) => segment ℝ (toReal (vert ((i.val : ℕ) : ZMod (m+2))))
          (toReal (vert (((i + (1:Fin (m+1))).val : ℕ) : ZMod (m+2))))) ∘ Fin.castSucc))
      = Set.iUnion (((fun i : Fin (m+2) => segment ℝ (toReal (vert i))
          (toReal (vert (i + (1:Fin (m+2)))))) ∘ Fin.castSucc) ∘ Fin.castSucc) := by
    apply Set.iUnion_congr
    intro i
    simp only [Function.comp_apply]
    rw [e2 i, e1 i]
  -- Diagonal-edge identifications.
  have hdiagL : (((Fin.last m : Fin (m+1)).val : ℕ) : ZMod (m+2)) = (m : ZMod (m+2)) := by
    simp [Fin.val_last]
  have hdiagL0 : (((Fin.last m + 1 : Fin (m+1)).val : ℕ) : ZMod (m+2)) = (0 : ZMod (m+2)) := by
    rw [show (Fin.last m + 1 : Fin (m+1)) = 0 by
      apply Fin.val_injective; simp [Fin.val_last, Fin.val_add_one]]
    simp
  have hearA1 : ((Fin.last m).castSucc : Fin (m+2)) = (m : ZMod (m+2)) := by
    apply Fin.val_injective
    rw [Fin.val_castSucc, Fin.val_last]
    show m = ZMod.val ((m : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  have hearA2 : ((Fin.last m).castSucc + 1 : Fin (m+2)) = ((m : ZMod (m+2)) + 1 : ZMod (m+2)) := by
    have h1 : ((m : ZMod (m+2)) + 1 : ZMod (m+2)) = ((m+1 : ℕ) : ZMod (m+2)) := by push_cast; ring
    rw [h1]
    apply Fin.val_injective
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def, Fin.val_castSucc, Fin.val_last]),
      Fin.val_castSucc, Fin.val_last]
    show m + 1 = ZMod.val ((m+1 : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  have hearB1 : (Fin.last (m+1) : Fin (m+2)) = ((m : ZMod (m+2)) + 1 : ZMod (m+2)) := by
    have h1 : ((m : ZMod (m+2)) + 1 : ZMod (m+2)) = ((m+1 : ℕ) : ZMod (m+2)) := by push_cast; ring
    rw [h1]
    apply Fin.val_injective
    rw [Fin.val_last]
    show m + 1 = ZMod.val ((m+1 : ℕ) : ZMod (m+2))
    rw [ZMod.val_natCast_of_lt (by omega)]
  have hearB2 : (Fin.last (m+1) + 1 : Fin (m+2)) = (0 : ZMod (m+2)) := by
    have h0 : (Fin.last (m+1) + 1 : Fin (m+2)) = (0 : Fin (m+2)) := by
      apply Fin.val_injective; simp [Fin.val_last, Fin.val_add_one]
    exact h0
  rw [hsub]
  simp only [Function.comp_apply, hearB2]
  simp only [hdiagL, hdiagL0, hearA1, hearA2, hearB1]
  -- Pure set algebra: the diagonal `v_m → v_0` (from deleteLast and the ear's reverse) coincides.
  rw [segment_symm ℝ (toReal (vert 0)) (toReal (vert (m : ZMod (m+2))))]
  ext x
  simp only [Set.mem_union]
  tauto

/-- **The packaged ear-clipping induction step.** Given (a) the ear triangle is simple and
positively oriented, (b) interior non-overlap `hdisj`, (c) the `I`/`B` lattice additivity
`hIB`, and (d) the recursive hypotheses (`h01` and the count identity) for the sub-polygon
`deleteLast P`, both `h01` and the count identity hold for `P`. Combines `h01_of_split`,
`PCI_of_split`, and the triangle bases (`triangle_h01_ae`, `PCI_triangle`) applied to the
ear. The hypotheses (a)–(c) are exactly the ear-validity geometry that remains. -/
lemma h01_PCI_step (P : LatticePolygon) (h : 2 ≤ P.n) (m : ℕ) (hm : P.n = m + 2)
    (hearS : (earTri P m hm).IsSimple) (hearO : (earTri P m hm).PositivelyOriented)
    (hdisj : ∀ q, ¬((deleteLast P h).winding q = 1 ∧ (earTri P m hm).winding q = 1))
    (hIB : (P.I : ℝ) + (P.B : ℝ) / 2 = ((deleteLast P h).I : ℝ) + ((earTri P m hm).I : ℝ)
        + (((deleteLast P h).B : ℝ) + ((earTri P m hm).B : ℝ)) / 2 - 1)
    (h01dL : ∀ᵐ q ∂MeasureTheory.volume,
      (deleteLast P h).winding q = 0 ∨ (deleteLast P h).winding q = 1)
    (PCIdL : (deleteLast P h).shoelace
      = ((deleteLast P h).I : ℝ) + ((deleteLast P h).B : ℝ) / 2 - 1) :
    (∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1)
      ∧ P.shoelace = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 := by
  have hear01 : ∀ᵐ q ∂MeasureTheory.volume,
      (earTri P m hm).winding q = 0 ∨ (earTri P m hm).winding q = 1 :=
    triangle_h01_ae (earTri P m hm) hearS rfl hearO
  have hearPCI : (earTri P m hm).shoelace
      = ((earTri P m hm).I : ℝ) + ((earTri P m hm).B : ℝ) / 2 - 1 :=
    PCI_triangle (earTri P m hm) rfl hearS hearO
  exact ⟨h01_of_split P h m hm h01dL hear01 hdisj, PCI_of_split P h m hm PCIdL hearPCI hIB⟩

/-- The polygon obtained by cyclically relabeling vertices to start at `+c`. Definitionally the
literal `⟨P.n, P.pos, fun i => P.vert (i + c)⟩`, so the `*_rotate` lemmas apply directly. -/
def rotateP (P : LatticePolygon) (c : ZMod P.n) : LatticePolygon :=
  ⟨P.n, P.pos, fun i => P.vert (i + c)⟩

@[simp] lemma rotateP_n (P : LatticePolygon) (c : ZMod P.n) : (rotateP P c).n = P.n := rfl

@[simp] lemma rotateP_vert (P : LatticePolygon) (c : ZMod P.n) (i : ZMod P.n) :
    (rotateP P c).vert i = P.vert (i + c) := rfl

lemma rotateP_winding (P : LatticePolygon) (c : ZMod P.n) (q : ℝ × ℝ) :
    (rotateP P c).winding q = P.winding q := winding_rotate P c q

lemma rotateP_shoelace (P : LatticePolygon) (c : ZMod P.n) :
    (rotateP P c).shoelace = P.shoelace := shoelace_rotate P c

lemma rotateP_I (P : LatticePolygon) (c : ZMod P.n) : (rotateP P c).I = P.I := I_rotate P c

lemma rotateP_B (P : LatticePolygon) (c : ZMod P.n) : (rotateP P c).B = P.B := B_rotate P c

/-- Rotated edge `i` is the original edge `i + c`. -/
lemma rotateP_edgeSeg (P : LatticePolygon) (c i : ZMod P.n) :
    (rotateP P c).edgeSeg i = P.edgeSeg (i + c) := edgeSeg_rotate P c i

/-- Rotation preserves positive orientation, since the shoelace is rotation-invariant. -/
lemma positivelyOriented_rotateP (P : LatticePolygon) (c : ZMod P.n)
    (hO : P.PositivelyOriented) : (rotateP P c).PositivelyOriented := by
  rw [LatticePolygon.PositivelyOriented, rotateP_shoelace]; exact hO

/-- Rotation preserves simplicity: the edges of `rotateP P c` are the bijective reindexing
`i ↦ i + c` of the edges of `P`. -/
lemma isSimple_rotateP (P : LatticePolygon) (c : ZMod P.n) (hS : P.IsSimple) :
    (rotateP P c).IsSimple := by
  obtain ⟨hdeg, hdisj, hadj⟩ := hS
  show (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).IsSimple
  -- `i ↦ i + c` is a bijection on `ZMod P.n`, so the rotated edges reindex `P`'s edges.
  have hedge : ∀ k : ZMod P.n,
      (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).edgeSeg k = P.edgeSeg (k + c) := by
    intro k
    simp only [LatticePolygon.edgeSeg]
    rw [show (k + 1 + c : ZMod P.n) = (k + c) + 1 from by ring]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    show P.vert (i + c) ≠ P.vert (i + 1 + c)
    rw [show (i + 1 + c : ZMod P.n) = (i + c) + 1 from by ring]
    exact hdeg (i + c)
  · intro i j hij hi1j hj1i
    rw [hedge, hedge]
    refine hdisj (i + c) (j + c) ?_ ?_ ?_
    · intro h; exact hij (add_right_cancel h)
    · intro h; apply hi1j
      have : (i + 1 + c : ZMod P.n) = j + c := by rw [← h]; ring
      exact add_right_cancel this
    · intro h; apply hj1i
      have : (j + 1 + c : ZMod P.n) = i + c := by rw [← h]; ring
      exact add_right_cancel this
  · intro i
    rw [hedge, hedge,
      show (⟨P.n, P.pos, fun i => P.vert (i + c)⟩ : LatticePolygon).vert (i + 1)
        = P.vert (i + 1 + c) from rfl,
      show (i + 1 + c : ZMod P.n) = (i + c) + 1 from by ring]
    exact hadj (i + c)

/-- The ear-validity predicate: deleting the last vertex of `R` yields a valid ear-clipping
split (smaller polygon simple+oriented, ear triangle simple+oriented, windings disjoint,
and the `I,B` counts add up). Bundles the geometric content left to an "ear provider". -/
def ValidEarLast (R : LatticePolygon) : Prop :=
  ∃ (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2),
    (deleteLast R h2).IsSimple ∧ (deleteLast R h2).PositivelyOriented ∧
    (earTri R m hm).IsSimple ∧ (earTri R m hm).PositivelyOriented ∧
    (∀ q, ¬((deleteLast R h2).winding q = 1 ∧ (earTri R m hm).winding q = 1)) ∧
    ((R.I : ℝ) + (R.B : ℝ) / 2 = ((deleteLast R h2).I : ℝ) + ((earTri R m hm).I : ℝ)
      + (((deleteLast R h2).B : ℝ) + ((earTri R m hm).B : ℝ)) / 2 - 1)

/-- An "ear provider" supplies, for every simple positively-oriented polygon with `≥ 4` vertices,
a rotation after which deleting the last vertex is a valid ear-clipping split. This bundles the
remaining geometric content (existence of an ear) as a hypothesis. -/
def EarProvider : Prop :=
  ∀ Q : LatticePolygon, Q.IsSimple → Q.PositivelyOriented → 4 ≤ Q.n →
    ∃ c : ZMod Q.n, ValidEarLast (rotateP Q c)

/-- **Ear-clipping strong induction.** Given an ear provider, every simple positively-oriented
lattice polygon satisfies the winding `0/1` dichotomy a.e. and the shoelace = `I + B/2 − 1`
identity. Proved by strong induction on the number of vertices, with the triangle base case
and the ear-clipping step. -/
theorem h01_and_PCI_of_provider (prov : EarProvider) :
    ∀ (k : ℕ) (P : LatticePolygon), P.n = k → P.IsSimple → P.PositivelyOriented →
      (∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1)
      ∧ P.shoelace = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro P hk hS hO
    have h3 : 3 ≤ k := hk ▸ simple_imp_three_le_n P hS
    rcases eq_or_lt_of_le h3 with h3eq | h4
    · -- base case: triangle
      exact ⟨triangle_h01_ae P hS (by omega) hO, PCI_triangle P (by omega) hS hO⟩
    · -- inductive step: k ≥ 4
      have hk4 : 4 ≤ P.n := by omega
      obtain ⟨c, hve⟩ := prov P hS hO hk4
      set R := rotateP P c with hR
      have hRS : R.IsSimple := isSimple_rotateP P c hS
      have hRO : R.PositivelyOriented := positivelyOriented_rotateP P c hO
      have hRn : R.n = k := by rw [hR, rotateP_n]; exact hk
      obtain ⟨h2, m, hm, hdLS, hdLO, hearS, hearO, hdisj, hIB⟩ := hve
      -- IH applied to deleteLast R
      have hdLn : (deleteLast R h2).n = k - 1 := by rw [deleteLast_n, hRn]
      have hlt : k - 1 < k := by omega
      obtain ⟨h01dL, PCIdL⟩ := IH (k - 1) hlt (deleteLast R h2) hdLn hdLS hdLO
      -- ear-clipping step on R
      obtain ⟨h01R, PCIR⟩ := h01_PCI_step R h2 m hm hearS hearO hdisj hIB h01dL PCIdL
      -- transfer back to P
      refine ⟨?_, ?_⟩
      · have : ∀ q, R.winding q = P.winding q := fun q => by rw [hR, rotateP_winding]
        filter_upwards [h01R] with q hq
        rwa [this q] at hq
      · rw [hR, rotateP_shoelace, rotateP_I, rotateP_B] at PCIR
        exact PCIR

/-- **Pick's theorem, modulo an ear provider.** Given an ear provider, every simple
positively-oriented lattice polygon has area `I + B/2 − 1`. -/
theorem pick_of_provider (prov : EarProvider) (P : LatticePolygon)
    (hsimple : P.IsSimple) (horient : P.PositivelyOriented) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 := by
  obtain ⟨h01, hPCI⟩ := h01_and_PCI_of_provider prov P.n P rfl hsimple horient
  exact pick_of_hypotheses_ae P h01 (greens_theorem P) hPCI

/-- Each edge segment is compact (image of `[0,1]` under a continuous affine map). -/
lemma isCompact_edgeSeg (P : LatticePolygon) (j : ZMod P.n) :
    IsCompact (P.edgeSeg j) := by
  rw [LatticePolygon.edgeSeg, segment_eq_image]
  exact (isCompact_Icc).image (by fun_prop)

/-- The vertex `v_m` does not lie on any edge other than the two incident ones. -/
lemma vert_notMem_edgeSeg (P : LatticePolygon) (hsimple : P.IsSimple) (m : ZMod P.n)
    (j : ZMod P.n) (hjm : j ≠ m) (hjm1 : j ≠ m - 1) :
    toReal (P.vert m) ∉ P.edgeSeg j := by
  have hmem_m : toReal (P.vert m) ∈ P.edgeSeg m := by
    rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _
  have hmem_m1 : toReal (P.vert m) ∈ P.edgeSeg (m - 1) := by
    rw [LatticePolygon.edgeSeg]
    have : (m - 1) + 1 = m := by ring
    rw [this]; exact right_mem_segment ℝ _ _
  by_cases hjm1' : j = m + 1
  · -- Case B: j = m+1, adjacent on the far side
    subst hjm1'
    intro hmem_j
    have hint : toReal (P.vert m) ∈ P.edgeSeg m ∩ P.edgeSeg (m + 1) := ⟨hmem_m, hmem_j⟩
    rw [hsimple.2.2 m] at hint
    have heq : toReal (P.vert m) = toReal (P.vert (m + 1)) := hint
    exact hsimple.1 m (toReal_injective heq)
  · -- Case A: j non-adjacent to m
    have hdisj := hsimple.2.1 m j (Ne.symm hjm) (Ne.symm hjm1') (by
      intro h; apply hjm1; rw [← h]; ring)
    exact fun hmem_j => (Set.disjoint_left.mp hdisj hmem_m) hmem_j

lemma exists_isolating_ball (P : LatticePolygon) (hsimple : P.IsSimple) (m : ZMod P.n) :
    ∃ r > 0, ∀ j : ZMod P.n, j ≠ m → j ≠ m - 1 →
      Disjoint (Metric.ball (toReal (P.vert m)) r) (P.edgeSeg j) := by
  -- The finite set of "bad" indices to avoid.
  classical
  set S : Finset (ZMod P.n) := Finset.univ.filter (fun j => j ≠ m ∧ j ≠ m - 1) with hS
  -- For each j ∈ S, infDist is positive.
  have hpos : ∀ j ∈ S, 0 < Metric.infDist (toReal (P.vert m)) (P.edgeSeg j) := by
    intro j hj
    rw [hS, Finset.mem_filter] at hj
    obtain ⟨_, hjm, hjm1⟩ := hj
    have hclosed : IsClosed (P.edgeSeg j) := (isCompact_edgeSeg P j).isClosed
    have hne : (P.edgeSeg j).Nonempty :=
      ⟨toReal (P.vert j), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩
    rw [← hclosed.notMem_iff_infDist_pos hne]
    exact vert_notMem_edgeSeg P hsimple m j hjm hjm1
  -- Take r := min over S of infDist, or 1 if S is empty.
  by_cases hSe : S.Nonempty
  · refine ⟨S.inf' hSe (fun j => Metric.infDist (toReal (P.vert m)) (P.edgeSeg j)), ?_, ?_⟩
    · exact Finset.lt_inf'_iff hSe |>.mpr hpos
    · intro j hjm hjm1
      have hjS : j ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ j, hjm, hjm1⟩
      rw [Set.disjoint_left]
      intro x hxball hxedge
      rw [Metric.mem_ball] at hxball
      have hle : S.inf' hSe (fun j => Metric.infDist (toReal (P.vert m)) (P.edgeSeg j))
          ≤ Metric.infDist (toReal (P.vert m)) (P.edgeSeg j) := Finset.inf'_le _ hjS
      have hdle : Metric.infDist (toReal (P.vert m)) (P.edgeSeg j)
          ≤ dist x (toReal (P.vert m)) := by
        rw [dist_comm]; exact Metric.infDist_le_dist_of_mem hxedge
      exact absurd (lt_of_le_of_lt (le_trans hle hdle) hxball) (lt_irrefl _)
  · refine ⟨1, one_pos, ?_⟩
    intro j hjm hjm1
    exact absurd ⟨j, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ j, hjm, hjm1⟩⟩ hSe

/-! ### Reduction of `winding ∈ {0,1}` to the crossing interleaving

The general-`n` polygonal Jordan dichotomy `winding ∈ {0,1}` reduces to a clean,
topology-free *count* inequality: at any swept point `(x,y)`, the number of
up-crossings of the rightward ray is at most one more than the number of
down-crossings, and at least as many. This is exactly the **interleaving** of the
horizontal-line crossings (between consecutive up-thresholds in `x`-order sits one
down-threshold and vice-versa) — the geometric heart of the Jordan argument that
`IsSimple` supplies. Everything *after* the interleaving is the arithmetic here. -/

/-- **Winding dichotomy from crossing interleaving.** If at the swept point `(x,y)`
the up-crossing count is sandwiched as `#down ≤ #up ≤ #down + 1`, then
`winding (x,y) ∈ {0,1}`. Immediate from `winding = #up − #down`
(`winding_eq_upCount_sub_downCount`). This isolates the single remaining
*geometric* input (the interleaving inequalities) from the arithmetic. -/
lemma winding_mem_zero_one_of_count (P : LatticePolygon) (x y : ℝ)
    (hup : (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card
      ≤ (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card + 1)
    (hdn : (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card
      ≤ (Finset.univ.filter fun i =>
        edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card) :
    P.winding (x, y) = 0 ∨ P.winding (x, y) = 1 := by
  rw [winding_eq_upCount_sub_downCount]; omega

/-- **A.e. reduction.** If the interleaving count inequalities hold at every
non-vertex height (the generic heights, whose complement is null by
`vertexHeights_finite`), then `winding ∈ {0,1}` almost everywhere. This is the
exact bridge from the geometric interleaving to the measure-theoretic `{0,1}`
statement consumed downstream (the non-generic heights form a null set). -/
lemma winding_ae_mem_zero_one_of_count (P : LatticePolygon)
    (hcount : ∀ x y : ℝ, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card
        ≤ (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card + 1) ∧
      ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card
        ≤ (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card)) :
    ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = 1 := by
  have hnull : MeasureTheory.volume {q : ℝ × ℝ | ∃ i, (toReal (P.vert i)).2 = q.2} = 0 :=
    Pick.vertexHeight_lines_null P
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hnull
  intro q hq
  by_contra hgen
  simp only [Set.mem_setOf_eq, not_exists] at hgen
  apply hq
  have hgen' : ∀ i, (toReal (P.vert i)).2 ≠ q.2 := fun i => hgen i
  obtain ⟨hu, hd⟩ := hcount q.1 q.2 hgen'
  have := winding_mem_zero_one_of_count P q.1 q.2 hu hd
  simpa using this

end Pick


/-! ### Alternation core (combinatorial heart of general-`n` Jordan)

The general-`n` `winding ∈ {0,1}` dichotomy reduces, at a generic height `y`, to
the alternation of the signed ray-crossings sorted by their `x`-threshold: a
right-to-left running sum of `±1` jumps stays in `{0,1}` iff the signs alternate
`+,-,+,-,…` (equivalently `-,+,-,+,…` read left-to-right). The lemmas here are
the **proven combinatorial content** of that alternation; the single remaining
*geometric* input is that an `IsSimple` polygon's crossings alternate. -/

namespace AlternationCore

/-- A list of `±1` signs *alternates* (consecutive entries differ in sign). -/
def Alternates : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => b = -a ∧ Alternates (b :: t)

/-- For an alternating list, the head determines the parity pattern of prefix
sums: if the list starts with value `v ∈ {±1}` then `(L.take k).sum` is `0` when
`k` is even and `v` when `k` is odd (for any `k`, clamped by the length but the
alternation makes the formula hold throughout). We track it via the running head
value. -/
lemma take_sum_eq_of_alternates : ∀ (L : List ℤ) (v : ℤ), Alternates L →
    (L ≠ [] → L.headI = v) → ∀ k,
    (L.take k).sum = (if Even (min k L.length) then 0 else v) := by
  intro L
  induction L using List.rec with
  | nil => intro v _ _ k; simp
  | cons a t IH =>
    intro v halt hhead k
    cases k with
    | zero => simp
    | succ k =>
      have hav : a = v := by simpa using hhead (by simp)
      subst hav
      cases t with
      | nil => cases k <;> simp [Nat.even_add_one, parity_simps]
      | cons b s =>
        -- alternation: b = -a, and (b :: s) alternates
        obtain ⟨hb, halts⟩ := halt
        have hIH := IH (-a) halts (by intro _; simpa using hb) k
        rw [List.take_succ_cons, List.sum_cons, hIH]
        simp only [List.length_cons]
        have hmin : min (k + 1) (s.length + 1 + 1) = min k (s.length + 1) + 1 := by omega
        rcases Nat.even_or_odd (min k (s.length + 1)) with he | ho
        · rw [if_pos he, if_neg (by rw [hmin]; simpa [Nat.even_add_one] using he)]
          ring
        · rw [if_neg (by simpa [Nat.not_even_iff_odd] using ho),
            if_pos (by rw [hmin]; simpa [Nat.even_add_one, Nat.not_even_iff_odd] using ho)]
          ring

/-- **Suffix sums of an alternating crossing list lie in `{0,1}`.** If an
alternating `±1` list starts with `-1`, every prefix sum is `0` or `-1`; hence
every *suffix* sum (the running winding count, swept right-to-left) is `0` or `1`.
This is the combinatorial content the geometric alternation supplies. -/
lemma prefixSums_mem_neg : ∀ (L : List ℤ), Alternates L →
    (L ≠ [] → L.headI = -1) →
    ∀ k, (L.take k).sum = 0 ∨ (L.take k).sum = -1 := by
  intro L halt hhead k
  rw [take_sum_eq_of_alternates L (-1) halt hhead k]
  split_ifs <;> [left; right] <;> rfl

/-- **Suffix sums of an alternating list with head `-1` and total sum `0` lie in
`{0,1}`.** Since `(L.drop k).sum = L.sum - (L.take k).sum = -(L.take k).sum`, and
prefix sums are in `{0,-1}`, suffix sums are in `{0,1}`. This is the form the
right-to-left winding sweep consumes. -/
lemma suffixSums_mem : ∀ (L : List ℤ), Alternates L →
    (L ≠ [] → L.headI = -1) → L.sum = 0 →
    ∀ k, (L.drop k).sum = 0 ∨ (L.drop k).sum = 1 := by
  intro L halt hhead hsum k
  have hsplit : (L.take k).sum + (L.drop k).sum = 0 := by
    rw [← List.sum_append, List.take_append_drop]; exact hsum
  rcases prefixSums_mem_neg L halt hhead k with h | h
  · left; omega
  · right; omega

/-- **Mirror suffix bound (head `+1`).** If an alternating `±1` list starts with
`+1` and sums to `0`, then every suffix sum lies in `{0,-1}`. (Prefix sums are in
`{0,1}` by `take_sum_eq_of_alternates`; suffix `= -prefix`.) -/
lemma suffixSums_mem_nonpos : ∀ (L : List ℤ), Alternates L →
    (L ≠ [] → L.headI = 1) → L.sum = 0 →
    ∀ k, (L.drop k).sum = 0 ∨ (L.drop k).sum = -1 := by
  intro L halt hhead hsum k
  have hsplit : (L.take k).sum + (L.drop k).sum = 0 := by
    rw [← List.sum_append, List.take_append_drop]; exact hsum
  have hpre : (L.take k).sum = 0 ∨ (L.take k).sum = 1 := by
    rw [take_sum_eq_of_alternates L 1 halt hhead k]; split_ifs <;> [left; right] <;> rfl
  rcases hpre with h | h
  · left; omega
  · right; omega

end AlternationCore

/-! ### STEP 1 — Curve-order alternation (vertex-side flip; no topology)

At a generic height `y`, assign each vertex `i` the boolean *side*
`side i := y < (vert i).2` ("`vert i` is above `y`"). An edge `i` **spans** `y`
iff its two endpoints lie on opposite sides (`side i ≠ side (i+1)`); when it
spans, it is an **up-edge** (`edgeWind = 1`) iff `vert (i+1)` is above
(`side (i+1) = true`), and a **down-edge** otherwise. The geometric heart of
STEP 1 is then a pure fact about the cyclic boolean sequence `side`: across a
*non-spanning* edge the side is unchanged, so between two consecutive spanning
edges (in cyclic vertex order, with only non-spanning edges in between) the side
is constant — hence the two spanning edges flip *to* opposite sides and therefore
have opposite up/down type. This is `spanning_consecutive_opposite_type` below;
it needs **no** simplicity and **no** topology, only the vertex-height ordering. -/

namespace Pick

open LatticePolygon

namespace LatticePolygon

variable (P : LatticePolygon)

/-- The `y`-side of a vertex: `true` iff the vertex lies strictly above the line
`{·.2 = y}`. The spanning/up/down structure is encoded by this boolean. -/
def vside (y : ℝ) (i : ZMod P.n) : Prop := y < (toReal (P.vert i)).2

/-- The sign of a spanning edge: `+1` for an up-edge (terminal vertex above `y`),
`-1` for a down-edge. -/
noncomputable def edgeSign (y : ℝ) (i : ZMod P.n) : ℤ :=
  if y < (toReal (P.vert (i + 1))).2 then 1 else -1

/-- The threshold (ray-crossing `x`) of edge `i` at height `y`. -/
noncomputable def edgeThr (y : ℝ) (i : ZMod P.n) : ℝ :=
  crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y

/-- The finset of edges spanning height `y` (either orientation). -/
noncomputable def spanningSet (y : ℝ) : Finset (ZMod P.n) :=
  Finset.univ.filter fun i =>
    ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
    ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)

end LatticePolygon

variable (P : LatticePolygon)

/-- An edge **spans** the generic height `y` exactly when its endpoints lie on
opposite sides — the "side flips" characterization of a crossing. -/
lemma spanning_iff_side_ne (y : ℝ) (i : ZMod P.n)
    (hi : (toReal (P.vert i)).2 ≠ y) (hi1 : (toReal (P.vert (i + 1))).2 ≠ y) :
    (((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    ↔ (P.vside y i ≠ P.vside y (i + 1)) := by
  unfold vside
  exact span_iff_above_ne _ _ y hi hi1

/-- **Side is constant across a non-spanning edge.** If edge `i` does not span the
generic height `y`, its two endpoints lie on the same side. The atomic constancy
fact powering the curve-order alternation. -/
lemma side_eq_of_not_spanning (y : ℝ) (i : ZMod P.n)
    (hi : (toReal (P.vert i)).2 ≠ y) (hi1 : (toReal (P.vert (i + 1))).2 ≠ y)
    (hns : ¬(((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))) :
    P.vside y i ↔ P.vside y (i + 1) := by
  rw [spanning_iff_side_ne P y i hi hi1] at hns
  exact iff_of_eq (not_ne_iff.mp hns)

/-- **Type of a spanning edge is determined by the side it flips *to*.** A
spanning edge is an up-edge (`edgeWind = 1` for small `x`) iff its terminal
vertex `vert (i+1)` is above `y`, i.e. iff `vside y (i+1)` holds. -/
lemma spanning_up_iff_side (y : ℝ) (i : ZMod P.n)
    (hi : (toReal (P.vert i)).2 ≠ y) (hi1 : (toReal (P.vert (i + 1))).2 ≠ y)
    (hsp : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)) :
    (((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)) ↔ P.vside y (i + 1) := by
  unfold vside
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    rcases hsp with hsp | hsp
    · exact hsp
    · exact absurd h (not_lt.mpr (le_of_lt hsp.1))

/-- **Constancy of side across a run of non-spanning edges.** If edges
`i, i+1, …, i+d-1` are all non-spanning at the generic height `y`, then the side
of `vert i` equals the side of `vert (i+d)` — the cumulative version of
`side_eq_of_not_spanning`. (Genericity at every traversed vertex is required.) -/
lemma side_eq_of_run (y : ℝ) (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) :
    ∀ d : ℕ,
      (∀ t : ℕ, t < d → ¬(((toReal (P.vert (i + t))).2 < y ∧
            y < (toReal (P.vert (i + t + 1))).2) ∨
          ((toReal (P.vert (i + t + 1))).2 < y ∧ y < (toReal (P.vert (i + t))).2))) →
      (P.vside y i ↔ P.vside y (i + d)) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d IH =>
    intro hrun
    have hstep : P.vside y (i + (d : ZMod P.n)) ↔ P.vside y ((i + (d : ZMod P.n)) + 1) :=
      side_eq_of_not_spanning P y (i + (d : ZMod P.n)) (hy _) (hy _) (hrun d (by omega))
    have hIH := IH (fun t ht => hrun t (by omega))
    have hcast : (i + ((d : ℕ) + 1 : ℕ) : ZMod P.n) = (i + (d : ZMod P.n)) + 1 := by
      push_cast; ring
    rw [hcast, ← hstep, hIH]

/-- **STEP 1 — Curve-order alternation (consecutive spanning edges have opposite
type).** Fix a generic height `y`. Suppose edge `i` spans `y`, edge `i+d`
(with `d ≥ 1`) spans `y`, and every edge strictly between them in cyclic vertex
order — `i+1, …, i+d-1` — does **not** span. Then the two spanning edges have
**opposite** up/down type: edge `i` is an up-edge iff edge `i+d` is a down-edge.

This is the topology-free combinatorial core of the polygonal Jordan argument:
as the boundary curve is traversed, the side relative to the line `{·.2 = y}`
flips exactly at each crossing and is constant in between, so successive crossings
necessarily reverse orientation. (No `IsSimple` is used; only the cyclic
vertex-height ordering at a generic height.) -/
lemma spanning_consecutive_opposite_type (y : ℝ)
    (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    (hspj : ((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2) ∨
      ((toReal (P.vert (i + d + 1))).2 < y ∧ y < (toReal (P.vert (i + d))).2))
    (hmid : ∀ t : ℕ, 1 ≤ t → t < d →
      ¬(((toReal (P.vert (i + t))).2 < y ∧ y < (toReal (P.vert (i + t + 1))).2) ∨
        ((toReal (P.vert (i + t + 1))).2 < y ∧ y < (toReal (P.vert (i + t))).2))) :
    (((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)) ↔
      ¬(((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2)) := by
  -- Work with `j := i + d`.  The run `i+1, …, i+(d-1)` of non-spanning edges keeps
  -- the side constant, so `side (i+1) ↔ side j`.
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hrun : P.vside y (i + 1) ↔ P.vside y (i + (((e : ℕ) + 1 : ℕ) : ZMod P.n)) := by
    have h := side_eq_of_run P y hy (i + 1) e (fun t ht => by
      have h := hmid (t + 1) (by omega) (by omega)
      rw [show (i + (↑(t + 1) : ZMod P.n)) = i + 1 + (↑t : ZMod P.n) by push_cast; ring] at h
      exact h)
    have hcast : (i + 1) + (e : ZMod P.n) = i + (((e : ℕ) + 1 : ℕ) : ZMod P.n) := by
      push_cast; ring
    rw [hcast] at h; exact h
  set j : ZMod P.n := i + (((e : ℕ) + 1 : ℕ) : ZMod P.n) with hj_def
  -- Edge `i` is up iff `side (i+1)`; edge `j` is up iff `side (j+1)`.
  have hi := spanning_up_iff_side P y i (hy i) (hy (i + 1)) hspi
  have hjup := spanning_up_iff_side P y j (hy j) (hy (j + 1)) hspj
  -- Edge `j` spans, so its side flips: `side j ≠ side (j+1)`.
  have hflip : P.vside y j ≠ P.vside y (j + 1) :=
    (spanning_iff_side_ne P y j (hy j) (hy (j + 1))).mp hspj
  -- The goal is already in `j`-form; assemble propositionally.
  rw [hi, hjup, hrun]
  -- Now: `side j ↔ ¬ side (j+1)`, given `side j ≠ side (j+1)`.
  constructor
  · intro h hc; exact hflip (by rw [eq_iff_iff]; exact ⟨fun _ => hc, fun _ => h⟩)
  · intro h
    by_contra hc
    exact hflip (by rw [eq_iff_iff]; exact ⟨fun hjj => absurd hjj hc, fun hj1 => absurd hj1 h⟩)

/-! ### STEP 4 — Wiring the count inequalities to the dichotomy (conditional)

The count inequalities `#down ≤ #up ≤ #down + 1` consumed by
`winding_ae_mem_zero_one_of_count` are equivalent, by
`winding = #up − #down` (`winding_eq_upCount_sub_downCount`), to the bound
`0 ≤ winding (x,y) ≤ 1` at the swept point. STEP 1–3 supply exactly this bound at
generic heights (the x-sorted alternation is `±1`-alternating with head `−1`, so
its suffix sums — the running winding count, swept right-to-left — lie in `{0,1}`
by `AlternationCore.prefixSums_mem_neg`). The lemmas here perform the **purely
mechanical** transfer in both directions, isolating the single remaining
*geometric* gap to the hypothesis `winding_bdd` below: *at every generic point the
winding is between `0` and `1`.* -/

/-- **Generic winding-bound ⇒ count inequalities.** At a generic height, the bound
`0 ≤ winding (x,y) ≤ 1` is *definitionally* the pair of count inequalities
`#up ≤ #down + 1` and `#down ≤ #up`, since `winding = #up − #down`. This is the
exact hypothesis shape required by `winding_ae_mem_zero_one_of_count`. -/
lemma count_ineqs_of_winding_bdd (x y : ℝ)
    (h0 : 0 ≤ P.winding (x, y)) (h1 : P.winding (x, y) ≤ 1) :
    ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card
        ≤ (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card + 1) ∧
      ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card
        ≤ (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card) := by
  rw [winding_eq_upCount_sub_downCount] at h0 h1
  omega

/-- **STEP 4 (mechanical) — generic winding-bound ⇒ a.e. dichotomy.** If at every
generic height (no vertex at that height) the swept winding satisfies
`0 ≤ winding (x,y) ≤ 1`, then `winding ∈ {0,1}` almost everywhere. This is the
clean bridge consuming the STEP 1–3 output: the *only* remaining geometric input
is `winding_bdd`, which is exactly what the curve-order alternation
(`spanning_consecutive_opposite_type`), its x-order transfer, and positive
orientation deliver via `AlternationCore.prefixSums_mem_neg`. -/
lemma winding_ae_mem_zero_one_of_winding_bdd
    (winding_bdd : ∀ x y : ℝ, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1) :
    ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = 1 := by
  apply Pick.winding_ae_mem_zero_one_of_count
  intro x y hgen
  obtain ⟨h0, h1⟩ := winding_bdd x y hgen
  exact count_ineqs_of_winding_bdd P x y h0 h1

/-! ### STEP A — Plumbing: winding-bound from an x-sorted alternating sign list

We isolate the whole remaining geometric content into a single hypothesis:
*the spanning edges, listed in increasing order of their crossing threshold,
have signs forming an `Alternates` list with head `-1`.* From this the bound
`0 ≤ winding (x,y) ≤ 1` is purely mechanical.

The bridge: `winding (x,y)` equals the sum of the signs of the spanning edges
whose threshold is `> x`. Listing the signs in increasing threshold order as
`L`, this is the *suffix* of `L` past the `k` thresholds that are `≤ x`. Since
`L` alternates from `-1` its total sum is `0` (even length: up/down counts are
equal), so each suffix sum `= -(prefix sum) ∈ {0,1}` by `prefixSums_mem_neg`. -/

/-- **Filter of a sorted list by an up-closed predicate is a `dropWhile`.** If `L`
is `R`-sorted and `p` is up-closed under `R` (so once `p` holds it holds onward),
then `L.filter p = L.dropWhile (fun a => !p a)`. -/
lemma filter_eq_dropWhile_of_sorted {α : Type*} (R : α → α → Prop) (p : α → Bool) :
    ∀ (L : List α), L.Pairwise R → (∀ a b, R a b → p a → p b) →
      L.filter p = L.dropWhile (fun a => !p a) := by
  intro L
  induction L with
  | nil => intro _ _; rfl
  | cons a t IH =>
    intro hpw hclosed
    rw [List.pairwise_cons] at hpw
    by_cases hpa : p a
    · -- every element of `a :: t` has `p`, so both sides are `a :: t`
      have hall : ∀ b ∈ (a :: t), p b := by
        intro b hb
        rcases List.mem_cons.mp hb with h | h
        · subst h; exact hpa
        · exact hclosed a b (hpw.1 b h) hpa
      rw [List.filter_eq_self.mpr hall,
        List.dropWhile_eq_self_iff.mpr (fun _ => by simp [hpa])]
    · rw [List.filter_cons_of_neg (by simp [hpa]),
        List.dropWhile_cons_of_pos (by simp [hpa])]
      exact IH hpw.2 hclosed

/-- **The signs of the spanning edges sum to `0`.** Up- and down-crossings are
equinumerous (`card_up_eq_card_down`), and `edgeSign` is `+1` on up-spanning,
`-1` on down-spanning edges. -/
lemma sum_edgeSign_spanning_eq_zero (y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    ∑ i ∈ P.spanningSet y, P.edgeSign y i = 0 := by
  classical
  unfold spanningSet edgeSign
  rw [Finset.sum_filter]
  have per : ∀ i,
      (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else -1) else 0)
      = (if (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else 0)
        - (if (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2 then 1 else 0) := by
    intro i
    have ha := hy i
    have hb := hy (i + 1)
    by_cases hup : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2
    · rw [if_pos (Or.inl hup), if_pos hup.2, if_pos ⟨le_of_lt hup.1, hup.2⟩,
        if_neg (fun h => absurd h.1 (not_le.mpr hup.2))]; ring
    · by_cases hdn : (toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2
      · rw [if_pos (Or.inr hdn), if_neg (not_lt.mpr (le_of_lt hdn.1)),
          if_neg (fun h => absurd h.1 (not_le.mpr hdn.2)),
          if_pos ⟨le_of_lt hdn.1, hdn.2⟩]; ring
      · rw [if_neg (by tauto)]
        rw [if_neg (fun h => hup ⟨lt_of_le_of_ne h.1 ha, h.2⟩),
          if_neg (fun h => hdn ⟨lt_of_le_of_ne h.1 hb, h.2⟩)]
        ring
  rw [Finset.sum_congr rfl fun i _ => per i, Finset.sum_sub_distrib]
  have e1 : (∑ i, if (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2 then (1:ℤ) else 0)
      = ((Finset.univ.filter fun i => (toReal (P.vert i)).2 ≤ y ∧
          y < (toReal (P.vert (i + 1))).2).card : ℤ) := by
    rw [Finset.card_filter]; push_cast; rfl
  have e2 : (∑ i, if (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2 then (1:ℤ) else 0)
      = ((Finset.univ.filter fun i => (toReal (P.vert (i + 1))).2 ≤ y ∧
          y < (toReal (P.vert i)).2).card : ℤ) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [e1, e2, card_up_eq_card_down P y, sub_self]

/-- **Winding as a sum over spanning edges.** At a generic height, the winding at
`(x,y)` is the sum of signs of the spanning edges whose threshold exceeds `x`. -/
lemma winding_eq_sum_spanning (x y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    P.winding (x, y)
      = ∑ i ∈ (P.spanningSet y).filter (fun i => x < P.edgeThr y i), P.edgeSign y i := by
  classical
  rw [winding_generic_sum P x y hy]
  unfold spanningSet edgeSign edgeThr
  rw [Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hsp : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) <;>
    by_cases hx : x < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y <;>
    simp only [hsp, hx, true_and, false_and, and_true, and_false, if_true, if_false,
      mul_one, mul_zero] <;>
    simp_all

/-- **STEP A — the winding bound from an x-sorted alternating sign list.** Suppose
the spanning edges at the generic height `y` are enumerated, in strictly increasing
order of their crossing threshold, by a `Nodup` list `L`; and the corresponding
sign list `L.map (edgeSign y)` alternates and (if nonempty) starts with `-1`. Then
at every `x`, `0 ≤ winding (x,y) ≤ 1`. This isolates the entire remaining geometric
gap to producing the alternating x-sorted list. -/
lemma winding_bdd_of_xsorted_alternates (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n))
    (hnodup : L.Nodup) (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (halt : AlternationCore.Alternates (L.map (P.edgeSign y)))
    (hhead : L.map (P.edgeSign y) ≠ [] → (L.map (P.edgeSign y)).headI = -1)
    (x : ℝ) : 0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1 := by
  classical
  -- The filter predicate (Bool) selecting thresholds to the right of `x`.
  set p : ZMod P.n → Bool := fun i => decide (x < P.edgeThr y i) with hp
  -- `winding (x,y)` is the sum of signs over spanning edges with threshold `> x`.
  have hw : P.winding (x, y) = ((L.filter p).map (P.edgeSign y)).sum := by
    rw [winding_eq_sum_spanning P x y hy]
    rw [show (P.spanningSet y).filter (fun i => x < P.edgeThr y i)
        = (L.filter p).toFinset by
      rw [List.toFinset_filter]
      ext i
      simp only [Finset.mem_filter, List.mem_toFinset, hmem i, hp, decide_eq_true_eq]]
    rw [List.sum_toFinset _ (hnodup.filter p)]
  -- The filter of a threshold-sorted list is a `dropWhile`, hence a `drop`.
  have hfilter : L.filter p = L.dropWhile (fun i => !p i) :=
    filter_eq_dropWhile_of_sorted _ p L hsorted
      (fun a b hab hpa => by
        simp only [hp, decide_eq_true_eq] at hpa ⊢; exact lt_trans hpa hab)
  -- `dropWhile q L = drop k L`, so its sign-sum is a suffix sum of `L.map edgeSign`.
  set q : ZMod P.n → Bool := fun i => !p i with hq
  have hdrop : (L.dropWhile q).map (P.edgeSign y)
      = (L.map (P.edgeSign y)).drop (L.takeWhile q).length := by
    have hsplit : L.map (P.edgeSign y)
        = (L.takeWhile q).map (P.edgeSign y) ++ (L.dropWhile q).map (P.edgeSign y) := by
      rw [← List.map_append, List.takeWhile_append_dropWhile]
    rw [hsplit, ← List.length_map (P.edgeSign y), List.drop_left]
  -- The total sign sum is `0` (up/down counts equal).
  have htot : (L.map (P.edgeSign y)).sum = 0 := by
    rw [← List.sum_toFinset _ hnodup,
      show L.toFinset = P.spanningSet y by ext i; rw [List.mem_toFinset, hmem i]]
    exact sum_edgeSign_spanning_eq_zero P y hy
  rw [hw, hfilter, hdrop]
  rcases AlternationCore.suffixSums_mem _ halt hhead htot (L.takeWhile q).length with h | h <;>
    rw [h] <;> omega

/-- **Mirror of STEP A (head `+1`).** With the same x-sorted alternating setup but
head `+1`, the winding satisfies `-1 ≤ winding (x,y) ≤ 0` at every `x`. Used to
derive the sign of the head from positive orientation: head `+1` would force
`winding ≤ 0` everywhere, contradicting positive area. -/
lemma winding_nonpos_of_xsorted_alternates (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n))
    (hnodup : L.Nodup) (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (halt : AlternationCore.Alternates (L.map (P.edgeSign y)))
    (hhead : L.map (P.edgeSign y) ≠ [] → (L.map (P.edgeSign y)).headI = 1)
    (x : ℝ) : -1 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 0 := by
  classical
  set p : ZMod P.n → Bool := fun i => decide (x < P.edgeThr y i) with hp
  have hw : P.winding (x, y) = ((L.filter p).map (P.edgeSign y)).sum := by
    rw [winding_eq_sum_spanning P x y hy]
    rw [show (P.spanningSet y).filter (fun i => x < P.edgeThr y i)
        = (L.filter p).toFinset by
      rw [List.toFinset_filter]
      ext i
      simp only [Finset.mem_filter, List.mem_toFinset, hmem i, hp, decide_eq_true_eq]]
    rw [List.sum_toFinset _ (hnodup.filter p)]
  have hfilter : L.filter p = L.dropWhile (fun i => !p i) :=
    filter_eq_dropWhile_of_sorted _ p L hsorted
      (fun a b hab hpa => by
        simp only [hp, decide_eq_true_eq] at hpa ⊢; exact lt_trans hpa hab)
  set q : ZMod P.n → Bool := fun i => !p i with hq
  have hdrop : (L.dropWhile q).map (P.edgeSign y)
      = (L.map (P.edgeSign y)).drop (L.takeWhile q).length := by
    have hsplit : L.map (P.edgeSign y)
        = (L.takeWhile q).map (P.edgeSign y) ++ (L.dropWhile q).map (P.edgeSign y) := by
      rw [← List.map_append, List.takeWhile_append_dropWhile]
    rw [hsplit, ← List.length_map (P.edgeSign y), List.drop_left]
  have htot : (L.map (P.edgeSign y)).sum = 0 := by
    rw [← List.sum_toFinset _ hnodup,
      show L.toFinset = P.spanningSet y by ext i; rw [List.mem_toFinset, hmem i]]
    exact sum_edgeSign_spanning_eq_zero P y hy
  rw [hw, hfilter, hdrop]
  rcases AlternationCore.suffixSums_mem_nonpos _ halt hhead htot (L.takeWhile q).length with h | h <;>
    rw [h] <;> omega

/-! ### STEP B — Sign of the head from orientation

`edgeSign` is always `±1`, so the head of a nonempty sorted sign list is `+1` or
`-1`. The mirror bound shows: if the head were `+1`, the winding would be `≤ 0`
*everywhere* on the line `{·.2 = y}`. So as soon as the winding is *positive*
anywhere on that line, the head must be `-1`. Positive orientation supplies such a
positive value (via `∫∫ winding = shoelace > 0`), pinning the head to `-1`. -/

/-- The head of the (nonempty) x-sorted sign list is `±1` (`edgeSign` is `±1`). -/
lemma headI_edgeSign_eq (y : ℝ) (L : List (ZMod P.n))
    (hne : L.map (P.edgeSign y) ≠ []) :
    (L.map (P.edgeSign y)).headI = 1 ∨ (L.map (P.edgeSign y)).headI = -1 := by
  cases L with
  | nil => simp at hne
  | cons a t =>
    simp only [List.map_cons, List.headI_cons]
    unfold edgeSign
    split_ifs <;> simp

/-- **STEP B — the head is `-1` once the winding is positive somewhere on the line.**
For an x-sorted alternating sign list at generic height `y`, if `winding (x₀,y) > 0`
for some `x₀`, then the sign list (if nonempty) starts with `-1` (a down-edge is
the leftmost crossing). Otherwise the mirror bound would force `winding ≤ 0`. -/
lemma head_neg_of_winding_pos (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n))
    (hnodup : L.Nodup) (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (halt : AlternationCore.Alternates (L.map (P.edgeSign y)))
    (x₀ : ℝ) (hpos : 0 < P.winding (x₀, y)) :
    L.map (P.edgeSign y) ≠ [] → (L.map (P.edgeSign y)).headI = -1 := by
  intro hne
  rcases headI_edgeSign_eq P y L hne with hhead | hhead
  · -- head = +1 would force winding ≤ 0 at x₀, contradiction
    exfalso
    have := (winding_nonpos_of_xsorted_alternates P y hy L hnodup hmem hsorted halt
      (fun _ => hhead) x₀).2
    linarith
  · exact hhead

/-- **STEP A+B capstone — `winding_bdd` from the two remaining geometric inputs.**
Assume that at every generic height `y` there is an x-sorted (`Nodup`,
threshold-increasing) enumeration `L` of the spanning edges whose sign list
alternates (input **C**, no-nesting), and that whenever some spanning edge exists
the winding is positive somewhere on the line `{·.2 = y}` (input **B'**,
leftmost-crossing-is-down). Then `0 ≤ winding (x,y) ≤ 1` at every generic point —
exactly the `winding_bdd` hypothesis feeding
`winding_ae_mem_zero_one_of_winding_bdd`. -/
lemma winding_bdd_of_alternation_and_pos
    (halt : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      ∃ L : List (ZMod P.n), L.Nodup ∧ (∀ i, i ∈ L ↔ i ∈ P.spanningSet y) ∧
        L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j) ∧
        AlternationCore.Alternates (L.map (P.edgeSign y)))
    (hposline : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y)) :
    ∀ x y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1 := by
  intro x y hy
  obtain ⟨L, hnodup, hmem, hsorted, hLalt⟩ := halt y hy
  -- Case: no spanning edge at all ⟹ the list is empty ⟹ winding is 0.
  by_cases hempty : L.map (P.edgeSign y) = []
  · have hLempty : L = [] := by simpa using hempty
    have hSempty : P.spanningSet y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi; rw [← hmem i, hLempty] at hi; exact List.not_mem_nil hi
    have : P.winding (x, y) = 0 := by
      rw [winding_eq_sum_spanning P x y hy]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hSempty] at hi; exact absurd hi.1 (Finset.notMem_empty i)
    rw [this]; exact ⟨le_refl 0, zero_le_one⟩
  · -- Nonempty: get the positive witness, pin the head to `-1`, apply STEP A.
    have hSne : (P.spanningSet y).Nonempty := by
      rw [← Finset.coe_nonempty]
      have : L ≠ [] := by intro h; rw [h] at hempty; simp at hempty
      obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil L this
      exact ⟨i, (hmem i).mp hi⟩
    obtain ⟨x₀, hx₀⟩ := hposline y hy hSne
    have hhead := head_neg_of_winding_pos P y hy L hnodup hmem hsorted hLalt x₀ hx₀
    exact winding_bdd_of_xsorted_alternates P y hy L hnodup hmem hsorted hLalt hhead x

/-! ### STEP C — Threshold-order non-nesting (the no-nesting geometric crux)

We prove that two **threshold-adjacent** spanning edges (no spanning edge crosses
between them in the `x`-order at height `y`) have **opposite** up/down sign. Over
all adjacent pairs this yields the `Alternates` sign list consumed by
`winding_bdd_of_xsorted_alternates`. The proof is the polygonal Jordan
no-self-crossing argument, built from concrete segment geometry. -/

/-- **A point on a non-spanning edge's segment is off the line `{·.2 = y}`.** Under
genericity (both endpoints off the line), a non-spanning edge keeps both endpoints
strictly on one side, so its whole segment avoids the line. This is the building
block that lets the boundary arc between two consecutive crossings stay in a closed
half-plane and meet the line only at its endpoints. -/
lemma seg_y_ne_of_not_spanning (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (ha : (toReal (P.vert i)).2 ≠ y) (hb : (toReal (P.vert (i + 1))).2 ≠ y)
    (hns : ¬(((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)))
    (q : ℝ × ℝ) (hq : q ∈ P.edgeSeg i) : q.2 ≠ y := by
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hq
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rcases lt_or_gt_of_ne ha with hlta | hgta <;> rcases lt_or_gt_of_ne hb with hltb | hgtb
  · intro h
    nlinarith [mul_pos (sub_pos.mpr hlta) (sub_pos.mpr hltb),
      mul_nonneg ht0 (le_of_lt (sub_pos.mpr hltb)),
      mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt (sub_pos.mpr hlta)),
      mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  · exact absurd (Or.inl ⟨hlta, hgtb⟩) hns
  · exact absurd (Or.inr ⟨hltb, hgta⟩) hns
  · intro h
    nlinarith [mul_pos (sub_pos.mpr hgta) (sub_pos.mpr hgtb),
      mul_nonneg ht0 (le_of_lt (sub_pos.mpr hgtb)),
      mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt (sub_pos.mpr hgta)),
      mul_nonneg ht0 (sub_nonneg.mpr ht1)]

/-- **The crossing point of a spanning edge lies on its segment.** Packaged form of
`crossThreshold_mem_segment(_down)` for `edgeThr`: the ray-crossing point
`(edgeThr y i, y)` is a genuine point of edge `i` (not just of its line). -/
lemma edgeThr_mem_edgeSeg (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)) :
    (P.edgeThr y i, y) ∈ P.edgeSeg i := by
  unfold LatticePolygon.edgeThr LatticePolygon.edgeSeg
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact crossThreshold_mem_segment _ _ y h1 h2
  · exact crossThreshold_mem_segment_down _ _ y h1 h2

/-- **The crossing point is the unique point of a spanning edge on the line.** Any
point of edge `i`'s segment at height `y` equals the threshold point
`(edgeThr y i, y)`. A spanning edge meets the line `{·.2 = y}` in exactly one
point. This pins the only place edge `i` can touch the line, the geometric input
that combines with `IsSimple` disjointness to control crossings. -/
lemma edgeThr_unique_cross (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    (q : ℝ × ℝ) (hq : q ∈ P.edgeSeg i) (hqy : q.2 = y) : q = (P.edgeThr y i, y) := by
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hq
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hqy' : (1 - t) * (toReal (P.vert i)).2 + t * (toReal (P.vert (i + 1))).2 = y := by
    simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using hqy
  have hd : (toReal (P.vert (i + 1))).2 - (toReal (P.vert i)).2 ≠ 0 := by
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (intro h; nlinarith)
  have ht : t = (y - (toReal (P.vert i)).2)
      / ((toReal (P.vert (i + 1))).2 - (toReal (P.vert i)).2) := by
    field_simp at hqy' ⊢; nlinarith
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    unfold LatticePolygon.edgeThr crossThreshold
    rw [ht]; field_simp; ring
  · simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using hqy

/-- `edgeSign y i = 1` iff edge `i` flips *to* the above-side, i.e. `vside y (i+1)`.
The sign is the boolean side of the terminal vertex. -/
lemma edgeSign_eq_one_iff (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) :
    P.edgeSign y i = 1 ↔ P.vside y (i + 1) := by
  unfold LatticePolygon.edgeSign LatticePolygon.vside
  by_cases h : y < (toReal (P.vert (i + 1))).2 <;> simp [h]

/-- `edgeSign y i = -1` iff edge `i`'s terminal vertex is **not** above `y`. -/
lemma edgeSign_eq_neg_one_iff (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) :
    P.edgeSign y i = -1 ↔ ¬ P.vside y (i + 1) := by
  unfold LatticePolygon.edgeSign LatticePolygon.vside
  by_cases h : y < (toReal (P.vert (i + 1))).2 <;> simp [h]

/-- **`edgeSign` form of curve-order alternation.** Two spanning edges `i` and
`i+d` (`d ≥ 1`) that are *consecutive in cyclic vertex order* (all edges strictly
between them are non-spanning) have **opposite** `edgeSign`. This is the
`edgeSign`-level restatement of `spanning_consecutive_opposite_type`, the bridge
from the topology-free vertex-order alternation to the `±1`-sign list. -/
lemma edgeSign_ne_of_consecutive_spanning (P : LatticePolygon) (y : ℝ)
    (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    (hspj : ((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2) ∨
      ((toReal (P.vert (i + d + 1))).2 < y ∧ y < (toReal (P.vert (i + d))).2))
    (hmid : ∀ t : ℕ, 1 ≤ t → t < d →
      ¬(((toReal (P.vert (i + t))).2 < y ∧ y < (toReal (P.vert (i + t + 1))).2) ∨
        ((toReal (P.vert (i + t + 1))).2 < y ∧ y < (toReal (P.vert (i + t))).2))) :
    P.edgeSign y i ≠ P.edgeSign y (i + d) := by
  have key := spanning_consecutive_opposite_type P y hy i d hd hspi hspj hmid
  rw [spanning_up_iff_side P y i (hy i) (hy (i + 1)) hspi,
      spanning_up_iff_side P y (i + d) (hy (i + d)) (hy (i + d + 1)) hspj,
      ← edgeSign_eq_one_iff, ← edgeSign_eq_one_iff] at key
  have hi : P.edgeSign y i = 1 ∨ P.edgeSign y i = -1 := by
    unfold LatticePolygon.edgeSign; split_ifs <;> simp
  have hj : P.edgeSign y (i + d) = 1 ∨ P.edgeSign y (i + d) = -1 := by
    unfold LatticePolygon.edgeSign; split_ifs <;> simp
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj]
  · exact absurd hj (key.mp hi)
  · decide
  · decide
  · exact absurd (key.mpr (by rw [hj]; decide)) (by rw [hi]; decide)

/-- An edge whose two endpoints are both (weakly) above height `y` stays (weakly)
above `y`: every point of `edgeSeg i` has `.2 ≥ y`. Convexity of the second
coordinate along the segment. Slab lemma feeding the boundary-arc construction. -/
lemma edgeSeg_above_of_endpoints_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (ha : y ≤ (toReal (P.vert i)).2) (hb : y ≤ (toReal (P.vert (i + 1))).2)
    (w : ℝ × ℝ) (hw : w ∈ P.edgeSeg i) : y ≤ w.2 := by
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hw
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hb),
    mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha)]

/-- An edge whose two endpoints are both **strictly** above height `y` stays strictly
above `y`. Strict companion of `edgeSeg_above_of_endpoints_above`: a convex combination
of two values both `> y` is `> y`. Used to show the middle run arc of `crossArc` — whose
intervening vertices are all strictly above `y` by genericity — never touches `{·.2=y}`. -/
lemma edgeSeg_gt_of_endpoints_gt (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (ha : y < (toReal (P.vert i)).2) (hb : y < (toReal (P.vert (i + 1))).2)
    (w : ℝ × ℝ) (hw : w ∈ P.edgeSeg i) : y < w.2 := by
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hw
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg ht0 (le_of_lt (sub_pos.mpr hb)),
    mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt (sub_pos.mpr ha))]

/-- An edge whose two endpoints are both (weakly) below height `y` stays (weakly)
below `y`. Symmetric companion of `edgeSeg_above_of_endpoints_above`. -/
lemma edgeSeg_below_of_endpoints_below (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (ha : (toReal (P.vert i)).2 ≤ y) (hb : (toReal (P.vert (i + 1))).2 ≤ y)
    (w : ℝ × ℝ) (hw : w ∈ P.edgeSeg i) : w.2 ≤ y := by
  rw [LatticePolygon.edgeSeg, segment_eq_image] at hw
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hb),
    mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha)]

/-- Continuity of the signed-distance-to-line functional `t ↦ cross (q-p) (γ t - p)`
along a continuous path `γ`. -/
lemma cross_continuous_along (p q : ℝ × ℝ) {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) :
    Continuous (fun t => cross (q - p) (γ t - p)) := by
  unfold cross
  fun_prop

/-- `cross (q - p) ((x, y) - p)` is affine in `x` with slope `-(q.2 - p.2)`. -/
lemma cross_horizontal_affine (p q : ℝ × ℝ) (x y : ℝ) :
    cross (q - p) ((x, y) - p) = -(q.2 - p.2) * x + cross (q - p) ((0, y) - p) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Any point of the segment `[p,q]` lies on the line through `p, q`
(`cross (q-p) (w-p) = 0`). -/
lemma cross_eq_zero_of_mem_segment (p q w : ℝ × ℝ) (hw : w ∈ segment ℝ p q) :
    cross (q - p) (w - p) = 0 := by
  rw [segment_eq_image] at hw
  obtain ⟨s, _, hs⟩ := hw
  subst hs
  simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

/-- A point `w` on the line through `p, q` (`cross (q-p) (w-p) = 0`) whose
`y`-coordinate lies in `[p.2, q.2]` (with `p.2 < q.2`) lies on the segment `[p, q]`. -/
lemma mem_segment_of_cross_zero (p q w : ℝ × ℝ) (hpq : p.2 < q.2)
    (hcross : cross (q - p) (w - p) = 0)
    (hlo : p.2 ≤ w.2) (hhi : w.2 ≤ q.2) :
    w ∈ segment ℝ p q := by
  have hd : (0:ℝ) < q.2 - p.2 := by linarith
  have hne : q.2 - p.2 ≠ 0 := ne_of_gt hd
  rw [segment_eq_image]
  refine ⟨(w.2 - p.2) / (q.2 - p.2), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one hd]; linarith
  · have hcr : (q.1 - p.1) * (w.2 - p.2) - (q.2 - p.2) * (w.1 - p.1) = 0 := by
      have := hcross
      simp only [cross, Prod.fst_sub, Prod.snd_sub] at this
      linarith
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      nlinarith [hcr]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      ring

/-- **Transversal-crossing lemma.** A continuous path `γ` joining `(a,y)` and `(b,y)`
that stays in the closed slab `{ y ≤ ·.2 ≤ q.2 }` must meet any segment `[p,q]` that
crosses the height-`y` line strictly between `x = a` and `x = b` (with `p` strictly
below `y` and `q` strictly above `y`).

Proof: `f t := cross (q-p) (γ t - p)` is continuous, with `f 0 = (q.2-p.2)(c-a) > 0`
and `f 1 = (q.2-p.2)(c-b) < 0` because the crossing column `c` lies strictly between
`a` and `b`. IVT yields `t` with `f t = 0`, i.e. `γ t` on the line through `p,q`;
the slab bound `y ≤ (γ t).2 ≤ q.2` upgrades this to membership in the segment `[p,q]`. -/
lemma path_above_meets_crossing_segment {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) (y a b : ℝ)
    (p q : ℝ × ℝ) (hp : p.2 < y) (hq : y < q.2)
    (h0 : γ 0 = (a, y)) (h1 : γ 1 = (b, y)) (hab : a < b)
    (haboveγ : ∀ t ∈ Set.Icc (0:ℝ) 1, y ≤ (γ t).2)
    (hbelowγ : ∀ t ∈ Set.Icc (0:ℝ) 1, (γ t).2 ≤ q.2)
    (c : ℝ) (hca : a < c) (hcb : c < b) (hc : (c, y) ∈ segment ℝ p q) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ segment ℝ p q := by
  set f : ℝ → ℝ := fun t => cross (q - p) (γ t - p) with hf
  have hfcont : Continuous f := cross_continuous_along p q hγ
  have hdy : (0:ℝ) < q.2 - p.2 := by linarith
  have hc0 : cross (q - p) ((c, y) - p) = 0 := cross_eq_zero_of_mem_segment p q _ hc
  have hfx : ∀ x, cross (q - p) ((x, y) - p) = (q.2 - p.2) * (c - x) := by
    intro x
    have h1 := cross_horizontal_affine p q x y
    have h2 := cross_horizontal_affine p q c y
    rw [hc0] at h2
    rw [h1]
    linarith [h2]
  have hf0 : f 0 = (q.2 - p.2) * (c - a) := by rw [hf]; simp only [h0]; exact hfx a
  have hf1 : f 1 = (q.2 - p.2) * (c - b) := by rw [hf]; simp only [h1]; exact hfx b
  have hf0pos : 0 < f 0 := by
    rw [hf0]; have hca' : 0 < c - a := by linarith
    positivity
  have hf1neg : f 1 < 0 := by
    rw [hf1]; have hcb' : c - b < 0 := by linarith
    exact mul_neg_of_pos_of_neg hdy hcb'
  have hmem : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨le_of_lt hf1neg, le_of_lt hf0pos⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1)
    hfcont.continuousOn hmem
  refine ⟨t, ht, ?_⟩
  apply mem_segment_of_cross_zero p q (γ t) (by linarith) hft
  · linarith [haboveγ t ht]
  · exact hbelowγ t ht

/-! ### STEP C scaffolding — boundary-arc parametrization and the transversal closure -/

/-- A continuous affine parametrization of edge `i`: `t ↦ (1-t)·vᵢ + t·vᵢ₊₁`. -/
noncomputable def edgeParam (P : LatticePolygon) (i : ZMod P.n) (t : ℝ) : ℝ × ℝ :=
  (1 - t) • toReal (P.vert i) + t • toReal (P.vert (i + 1))

lemma edgeParam_continuous (P : LatticePolygon) (i : ZMod P.n) :
    Continuous (edgeParam P i) := by
  unfold edgeParam
  fun_prop

lemma edgeParam_zero (P : LatticePolygon) (i : ZMod P.n) :
    edgeParam P i 0 = toReal (P.vert i) := by
  simp [edgeParam]

lemma edgeParam_one (P : LatticePolygon) (i : ZMod P.n) :
    edgeParam P i 1 = toReal (P.vert (i + 1)) := by
  simp [edgeParam]

lemma edgeParam_mem_edgeSeg (P : LatticePolygon) (i : ZMod P.n) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : edgeParam P i t ∈ P.edgeSeg i := by
  rw [LatticePolygon.edgeSeg, segment_eq_image]
  exact ⟨t, ht, rfl⟩

/-- Concatenate two raw `[0,1]`-parametrizations: run `f` on `[0,½]` and `g` on
`[½,1]` (each sped up by 2). Reusable continuous gluing for boundary arcs. -/
noncomputable def gluePath (f g : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  if t ≤ (1:ℝ)/2 then f (2 * t) else g (2 * t - 1)

lemma gluePath_continuous {f g : ℝ → ℝ × ℝ} (hf : Continuous f) (hg : Continuous g)
    (hmatch : f 1 = g 0) : Continuous (gluePath f g) := by
  unfold gluePath
  apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
  intro x hx; subst hx; norm_num [hmatch]

lemma gluePath_zero {f g : ℝ → ℝ × ℝ} : gluePath f g 0 = f 0 := by
  simp [gluePath]

lemma gluePath_one {f g : ℝ → ℝ × ℝ} : gluePath f g 1 = g 1 := by
  unfold gluePath; norm_num

/-- Every value of `gluePath f g` over `[0,1]` is a value of `f` over `[0,1]` or of
`g` over `[0,1]`. The slab/range transfer for the gluing. -/
lemma gluePath_mem_range {f g : ℝ → ℝ × ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (∃ s ∈ Set.Icc (0:ℝ) 1, gluePath f g t = f s) ∨
      (∃ s ∈ Set.Icc (0:ℝ) 1, gluePath f g t = g s) := by
  obtain ⟨ht0, ht1⟩ := ht
  unfold gluePath
  by_cases h : t ≤ (1:ℝ)/2
  · left; exact ⟨2 * t, ⟨by linarith, by linarith⟩, by rw [if_pos h]⟩
  · right; exact ⟨2 * t - 1, ⟨by linarith, by linarith⟩, by rw [if_neg h]⟩

/-- The boundary **run arc** traversing edges `i, i+1, …, i+(d-1)` as one continuous
`[0,1]`-parametrization. `runParam P i 0` is the constant at `vert i`; each extra
edge is glued on by `gluePath`. -/
noncomputable def runParam (P : LatticePolygon) (i : ZMod P.n) : ℕ → ℝ → ℝ × ℝ
  | 0 => fun _ => toReal (P.vert i)
  | (d + 1) => gluePath (runParam P i d) (edgeParam P (i + (d : ZMod P.n)))

lemma runParam_zero_pt (P : LatticePolygon) (i : ZMod P.n) :
    ∀ d : ℕ, runParam P i d 0 = toReal (P.vert i)
  | 0 => rfl
  | (d + 1) => by rw [runParam, gluePath_zero, runParam_zero_pt P i d]

lemma runParam_one_pt (P : LatticePolygon) (i : ZMod P.n) :
    ∀ d : ℕ, runParam P i d 1 = toReal (P.vert (i + (d : ZMod P.n)))
  | 0 => by simp [runParam]
  | (d + 1) => by
      rw [runParam, gluePath_one, edgeParam_one]
      congr 2; push_cast; ring

lemma runParam_continuous (P : LatticePolygon) (i : ZMod P.n) :
    ∀ d : ℕ, Continuous (runParam P i d)
  | 0 => continuous_const
  | (d + 1) => by
      refine gluePath_continuous (runParam_continuous P i d)
        (edgeParam_continuous P _) ?_
      rw [runParam_one_pt P i d, edgeParam_zero]

/-- **Every point of the run arc lies on one of its edges.** For `t ∈ [0,1]`,
`runParam P i d t` belongs to `edgeSeg (i+k)` for some `k < d` (or, when `d = 0`,
equals `vert i`). The range-tracking lemma for the slab bound. -/
lemma runParam_mem_edges (P : LatticePolygon) (i : ZMod P.n) :
    ∀ (d : ℕ) {t : ℝ}, t ∈ Set.Icc (0:ℝ) 1 →
      runParam P i d t = toReal (P.vert i) ∨
        ∃ k : ℕ, k < d ∧ runParam P i d t ∈ P.edgeSeg (i + (k : ZMod P.n))
  | 0, t, _ => Or.inl rfl
  | (d + 1), t, ht => by
      rw [runParam]
      rcases gluePath_mem_range (f := runParam P i d)
          (g := edgeParam P (i + (d : ZMod P.n))) ht with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
      · rw [heq]
        rcases runParam_mem_edges P i d hs with h | ⟨k, hk, hmem⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, by omega, hmem⟩
      · rw [heq]
        exact Or.inr ⟨d, by omega, edgeParam_mem_edgeSeg P _ hs⟩

/-- **The run arc passes through every one of its vertices.** The run arc
`runParam P j L` traverses edges `j, j+1, …, j+(L−1)`, so for each `m ≤ L` it reaches
the vertex `v_{j+m}` at some parameter `s ∈ [0,1]` (`m = 0` at `s = 0`, `m = L` at
`s = 1`, intermediate vertices at the gluing points). The lemma that recovers a height
bound on every interior arc vertex from a uniform height bound on the run arc. -/
lemma runParam_hits_vertex (P : LatticePolygon) (j : ZMod P.n) :
    ∀ (L m : ℕ), m ≤ L →
      ∃ s ∈ Set.Icc (0:ℝ) 1, runParam P j L s = toReal (P.vert (j + (m : ZMod P.n))) := by
  intro L
  induction L with
  | zero =>
    intro m hm
    refine ⟨0, by norm_num, ?_⟩
    rw [runParam_zero_pt]; simp [show m = 0 by omega]
  | succ e ih =>
    intro m hm
    rcases Nat.lt_or_ge m (e+1) with hlt | hge
    · obtain ⟨s, hs, hseq⟩ := ih m (by omega)
      refine ⟨s/2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      rw [runParam, gluePath, if_pos (by linarith [hs.2]), show 2 * (s/2) = s by ring]
      exact hseq
    · have hm' : m = e + 1 := by omega
      refine ⟨1, by norm_num, ?_⟩
      rw [runParam_one_pt, hm']

/-- **Slab-free transversal-crossing lemma.** A continuous path `γ` joining `(a,y)`
and `(b,y)` whose crossing column `c` (of the line through `p,q`, with `p` strictly
below and `q` strictly above `y`) lies strictly between `a` and `b` must meet the
**full line** through `p,q`: there is `t ∈ [0,1]` with `cross (q-p) (γ t − p) = 0`.
No upper slab bound is needed — this is the variant that survives an arc rising above
`q`. (Combine with a lower bound `y ≤ (γ t).2` and an upper bound to upgrade to
segment membership via `mem_segment_of_cross_zero`.) -/
lemma path_meets_crossing_line {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) (y a b : ℝ)
    (p q : ℝ × ℝ) (hp : p.2 < y) (hq : y < q.2)
    (h0 : γ 0 = (a, y)) (h1 : γ 1 = (b, y)) (hab : a < b)
    (c : ℝ) (hca : a < c) (hcb : c < b) (hc : (c, y) ∈ segment ℝ p q) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, cross (q - p) (γ t - p) = 0 := by
  set f : ℝ → ℝ := fun t => cross (q - p) (γ t - p) with hf
  have hfcont : Continuous f := cross_continuous_along p q hγ
  have hdy : (0:ℝ) < q.2 - p.2 := by linarith
  have hc0 : cross (q - p) ((c, y) - p) = 0 := cross_eq_zero_of_mem_segment p q _ hc
  have hfx : ∀ x, cross (q - p) ((x, y) - p) = (q.2 - p.2) * (c - x) := by
    intro x
    have h1 := cross_horizontal_affine p q x y
    have h2 := cross_horizontal_affine p q c y
    rw [hc0] at h2; rw [h1]; linarith [h2]
  have hf0 : f 0 = (q.2 - p.2) * (c - a) := by rw [hf]; simp only [h0]; exact hfx a
  have hf1 : f 1 = (q.2 - p.2) * (c - b) := by rw [hf]; simp only [h1]; exact hfx b
  have hf0pos : 0 < f 0 := by
    rw [hf0]; have hca' : 0 < c - a := by linarith
    positivity
  have hf1neg : f 1 < 0 := by
    rw [hf1]; exact mul_neg_of_pos_of_neg hdy (by linarith)
  have hmem : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨le_of_lt hf1neg, le_of_lt hf0pos⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1)
    hfcont.continuousOn hmem
  exact ⟨t, ht, hft⟩

/-- **Slab bound for an all-above run arc.** If every edge `i, …, i+(d-1)` keeps both
endpoints weakly above `y`, the whole run arc stays weakly above `y`. -/
lemma runParam_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hi : y ≤ (toReal (P.vert i)).2)
    (hedges : ∀ k : ℕ, k < d → y ≤ (toReal (P.vert (i + (k : ZMod P.n) + 1))).2) :
    ∀ {t : ℝ}, t ∈ Set.Icc (0:ℝ) 1 → y ≤ (runParam P i d t).2 := by
  intro t ht
  rcases runParam_mem_edges P i d ht with h | ⟨k, hk, hmem⟩
  · rw [h]; exact hi
  · -- both endpoints of edge `i+k` are ≥ y
    have hlo : y ≤ (toReal (P.vert (i + (k : ZMod P.n)))).2 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simpa using hi
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := hedges k' (by omega)
        rw [show (i + ((k' + 1 : ℕ) : ZMod P.n)) = (i + (k' : ZMod P.n) + 1) by
          push_cast; ring]
        exact this
    have hhi : y ≤ (toReal (P.vert (i + (k : ZMod P.n) + 1))).2 := hedges k hk
    exact edgeSeg_above_of_endpoints_above P y (i + (k : ZMod P.n)) hlo hhi _ hmem

/-- **Strict slab bound for an all-strictly-above run arc.** If `vert i` and every
edge endpoint `i, …, i+(d-1), i+d` is *strictly* above `y`, the whole run arc stays
strictly above `y`. The strict companion of `runParam_above`, for the middle piece of
`crossArc` whose vertices are all strictly above `y` (none of them spanning). -/
lemma runParam_gt_y (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hi : y < (toReal (P.vert i)).2)
    (hedges : ∀ k : ℕ, k < d → y < (toReal (P.vert (i + (k : ZMod P.n) + 1))).2) :
    ∀ {t : ℝ}, t ∈ Set.Icc (0:ℝ) 1 → y < (runParam P i d t).2 := by
  intro t ht
  rcases runParam_mem_edges P i d ht with h | ⟨k, hk, hmem⟩
  · rw [h]; exact hi
  · have hlo : y < (toReal (P.vert (i + (k : ZMod P.n)))).2 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simpa using hi
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := hedges k' (by omega)
        rw [show (i + ((k' + 1 : ℕ) : ZMod P.n)) = (i + (k' : ZMod P.n) + 1) by
          push_cast; ring]
        exact this
    have hhi : y < (toReal (P.vert (i + (k : ZMod P.n) + 1))).2 := hedges k hk
    exact edgeSeg_gt_of_endpoints_gt P y (i + (k : ZMod P.n)) hlo hhi _ hmem

/-- **Existence of the next spanning edge in vertex order.** If edge `i + D`
(`D ≥ 1`) spans `y`, there is a *minimal* `d` with `1 ≤ d ≤ D`, edge `i+d`
spanning, and all edges strictly between (`i+1, …, i+d-1`) non-spanning. This is
the combinatorial extraction feeding `edgeSign_ne_of_consecutive_spanning`:
between any two spanning edges there is a first spanning edge, and the signs flip
across that gap. -/
lemma next_spanning_exists (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (D : ℕ) (hD : 1 ≤ D)
    (hspj : (((toReal (P.vert (i + D))).2 < y ∧ y < (toReal (P.vert (i + D + 1))).2) ∨
      ((toReal (P.vert (i + D + 1))).2 < y ∧ y < (toReal (P.vert (i + D))).2))) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧
      (((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2) ∨
        ((toReal (P.vert (i + d + 1))).2 < y ∧ y < (toReal (P.vert (i + d))).2)) ∧
      (∀ t : ℕ, 1 ≤ t → t < d →
        ¬(((toReal (P.vert (i + t))).2 < y ∧ y < (toReal (P.vert (i + t + 1))).2) ∨
          ((toReal (P.vert (i + t + 1))).2 < y ∧ y < (toReal (P.vert (i + t))).2))) := by
  classical
  let S : Set ℕ := {d | 1 ≤ d ∧ d ≤ D ∧
    (((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2) ∨
      ((toReal (P.vert (i + d + 1))).2 < y ∧ y < (toReal (P.vert (i + d))).2))}
  have hSne : S.Nonempty := ⟨D, hD, le_refl D, hspj⟩
  obtain ⟨d, ⟨hd1, hdD, hdsp⟩, hdmin⟩ := Nat.lt_wfRel.wf.has_min S hSne
  refine ⟨d, hd1, hdD, hdsp, ?_⟩
  intro t ht1 htd hcon
  exact hdmin t ⟨ht1, le_trans (le_of_lt htd) hdD, hcon⟩ htd

/-- The `.2` coordinate of `edgeParam` as an explicit affine combination. -/
lemma edgeParam_snd (P : LatticePolygon) (i : ZMod P.n) (t : ℝ) :
    (edgeParam P i t).2 = (1 - t) * (toReal (P.vert i)).2 + t * (toReal (P.vert (i+1))).2 := by
  simp [edgeParam, Prod.snd_add, Prod.smul_snd, smul_eq_mul]

/-- **Convexity of height along a sub-arc of an edge.** If both endpoints of the
sub-arc `edgeParam i` over `[s₀, s₁]` are (weakly) above `y`, every interior point
is too. The single-edge convexity that, applied to the sub-edge from a crossing
point `(edgeThr y i, y)` (height `= y`) to the above-vertex, keeps the partial edge
in the closed upper slab `{·.2 ≥ y}`. Building block for the boundary-arc slab
bound feeding the transversal-crossing lemmas. -/
lemma edgeParam_above_of_endpoints (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (s₀ s₁ : ℝ) (hs : s₀ ≤ s₁)
    (h0 : y ≤ (edgeParam P i s₀).2) (h1 : y ≤ (edgeParam P i s₁).2)
    {s : ℝ} (hsl : s₀ ≤ s) (hsr : s ≤ s₁) : y ≤ (edgeParam P i s).2 := by
  simp only [edgeParam, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at *
  set a := (toReal (P.vert i)).2
  set b := (toReal (P.vert (i+1))).2
  rcases eq_or_lt_of_le hs with heq | hlt
  · have : s = s₀ := le_antisymm (by rw [← heq] at hsr; exact hsr) hsl
    rw [this]; exact h0
  · set lam := (s - s₀)/(s₁ - s₀) with hlam
    have hc0 : (0:ℝ) ≤ lam := by rw [hlam]; positivity
    have hc1 : lam ≤ 1 := by rw [hlam, div_le_one (by linarith)]; linarith
    have hid : (1 - s) * a + s * b
        = (1 - lam) * ((1 - s₀)*a + s₀*b) + lam * ((1 - s₁)*a + s₁*b) := by
      rw [hlam]; field_simp; ring
    rw [hid]
    have t1 : (0:ℝ) ≤ (1 - lam) * ((1 - s₀)*a + s₀*b - y) := mul_nonneg (by linarith) (by linarith)
    have t2 : (0:ℝ) ≤ lam * ((1 - s₁)*a + s₁*b - y) := mul_nonneg hc0 (by linarith)
    nlinarith [t1, t2]

/-- **Strict convexity of height along a sub-arc of an edge.** If one endpoint of the
sub-arc `edgeParam i` over `[s₀, s₁]` is weakly above `y` and the *other* is strictly
above `y`, then every *interior* point `s ∈ (s₀, s₁)` is strictly above `y`. The strict
companion of `edgeParam_above_of_endpoints`: applied to a partial edge from a crossing
point (height `= y`) up to a vertex strictly above `y`, it shows the open part of the
partial edge is strictly inside the upper slab `{·.2 > y}` — the analytic core of
`crossArc` touching the line `{·.2 = y}` only at its two endpoints. -/
lemma edgeParam_above_strict (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (s₀ s₁ : ℝ) (h0 : y ≤ (edgeParam P i s₀).2) (h1 : y ≤ (edgeParam P i s₁).2)
    (hstrict : y < (edgeParam P i s₀).2 ∨ y < (edgeParam P i s₁).2)
    {s : ℝ} (hsl : s₀ < s) (hsr : s < s₁) : y < (edgeParam P i s).2 := by
  simp only [edgeParam, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at *
  set a := (toReal (P.vert i)).2
  set b := (toReal (P.vert (i+1))).2
  have hs01 : s₀ < s₁ := lt_trans hsl hsr
  set lam := (s - s₀)/(s₁ - s₀) with hlam
  have hpos : (0:ℝ) < s₁ - s₀ := by linarith
  have hc0 : (0:ℝ) < lam := by rw [hlam]; positivity
  have hc1 : lam < 1 := by rw [hlam, div_lt_one hpos]; linarith
  have hid : (1 - s) * a + s * b
      = (1 - lam) * ((1 - s₀)*a + s₀*b) + lam * ((1 - s₁)*a + s₁*b) := by
    rw [hlam]; field_simp; ring
  rw [hid]
  rcases hstrict with hL | hR
  · have t1 : (0:ℝ) < (1 - lam) * ((1 - s₀)*a + s₀*b - y) :=
      mul_pos (by linarith) (by linarith)
    have t2 : (0:ℝ) ≤ lam * ((1 - s₁)*a + s₁*b - y) := mul_nonneg (by linarith) (by linarith)
    nlinarith [t1, t2]
  · have t1 : (0:ℝ) ≤ (1 - lam) * ((1 - s₀)*a + s₀*b - y) :=
      mul_nonneg (by linarith) (by linarith)
    have t2 : (0:ℝ) < lam * ((1 - s₁)*a + s₁*b - y) := mul_pos hc0 (by linarith)
    nlinarith [t1, t2]

/-- The crossing parameter `t* = (y − vᵢ.2)/(vᵢ₊₁.2 − vᵢ.2)` sends `edgeParam i` to
the threshold point `(edgeThr y i, y)`: `edgeParam i t* = (edgeThr y i, y)`. -/
lemma edgeParam_crossParam (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2) :
    edgeParam P i ((y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2))
      = (P.edgeThr y i, y) := by
  have hd : (toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2 ≠ 0 := sub_ne_zero.mpr hne
  apply Prod.ext
  · simp only [edgeParam, LatticePolygon.edgeThr, crossThreshold, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul]
    field_simp; ring
  · simp only [edgeParam, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp; ring

/-- The crossing parameter `t*` of a spanning edge lies strictly in `(0,1)`. -/
lemma crossParam_mem_Ioo (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)) :
    0 < (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2) ∧
      (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2) < 1 := by
  rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hd : (0:ℝ) < (toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2 := by linarith
    constructor
    · positivity
    · rw [div_lt_one hd]; linarith
  · have hd : (toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2 < 0 := by linarith
    constructor
    · apply div_pos_of_neg_of_neg <;> linarith
    · rw [div_lt_one_of_neg hd]; linarith

/-- **Up-edge partial arc stays above `y`.** For an up-spanning edge `i`
(`vᵢ` below, `vᵢ₊₁` above), the sub-arc `edgeParam i` over `[t*, 1]` — from the
crossing point `(edgeThr y i, y)` up to the top vertex `vᵢ₊₁` — keeps height `≥ y`. -/
lemma edgeParam_above_up (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {s : ℝ}
    (hsl : (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2) ≤ s)
    (hsr : s ≤ 1) : y ≤ (edgeParam P i s).2 := by
  set t0 := (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2) with ht0
  have hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by intro h; linarith [hsp.1, hsp.2]
  have h0 : y ≤ (edgeParam P i t0).2 := by rw [ht0, edgeParam_crossParam P y i hne]
  have h1 : y ≤ (edgeParam P i 1).2 := by rw [edgeParam_one]; linarith [hsp.2]
  exact edgeParam_above_of_endpoints P y i t0 1 (le_trans hsl hsr) h0 h1 hsl hsr

/-- **Down-edge partial arc stays above `y`.** For a down-spanning edge `i`
(`vᵢ` above, `vᵢ₊₁` below), the sub-arc `edgeParam i` over `[0, t*]` — from the top
vertex `vᵢ` down to the crossing point `(edgeThr y i, y)` — keeps height `≥ y`. -/
lemma edgeParam_above_down (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)
    {s : ℝ} (hsl : 0 ≤ s)
    (hsr : s ≤ (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2)) :
    y ≤ (edgeParam P i s).2 := by
  set t0 := (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2) with ht0
  have hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by intro h; linarith [hsp.1, hsp.2]
  have h0 : y ≤ (edgeParam P i 0).2 := by rw [edgeParam_zero]; linarith [hsp.2]
  have h1 : y ≤ (edgeParam P i t0).2 := by rw [ht0, edgeParam_crossParam P y i hne]
  exact edgeParam_above_of_endpoints P y i 0 t0 (le_trans hsl hsr) h0 h1 hsl hsr

/-- The crossing parameter `t* = (y − vᵢ.2)/(vᵢ₊₁.2 − vᵢ.2)` of edge `i` at height `y`. -/
noncomputable def crossParamT (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) : ℝ :=
  (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2)

/-- **First partial arc.** Reparametrize edge `i` to run from the crossing point
`(edgeThr y i, y)` (at param `t*`) up to vertex `vᵢ₊₁` (at param `1`), over `[0,1]`. -/
noncomputable def firstPartial (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (s : ℝ) : ℝ × ℝ :=
  edgeParam P i (crossParamT P y i + s * (1 - crossParamT P y i))

lemma firstPartial_continuous (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) :
    Continuous (firstPartial P y i) := by
  unfold firstPartial
  exact (edgeParam_continuous P i).comp (by fun_prop)

lemma firstPartial_zero (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2) :
    firstPartial P y i 0 = (P.edgeThr y i, y) := by
  unfold firstPartial crossParamT
  rw [show (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2)
      + 0 * (1 - (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2))
      = (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2) by ring]
  exact edgeParam_crossParam P y i hne

lemma firstPartial_one (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) :
    firstPartial P y i 1 = toReal (P.vert (i+1)) := by
  unfold firstPartial
  rw [show crossParamT P y i + 1 * (1 - crossParamT P y i) = 1 by ring]
  exact edgeParam_one P i

/-- For an up-spanning edge `i`, the reparam argument `t* + s(1−t*)` lies in `[t*,1] ⊆ [0,1]`. -/
lemma firstPartial_arg_mem (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    crossParamT P y i ≤ crossParamT P y i + s * (1 - crossParamT P y i) ∧
      crossParamT P y i + s * (1 - crossParamT P y i) ≤ 1 := by
  obtain ⟨hs0, hs1⟩ := hs
  have ht := crossParam_mem_Ioo P y i (Or.inl hsp)
  rw [show crossParamT P y i =
      (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2) from rfl]
  set t0 := (y - (toReal (P.vert i)).2) / ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2)
  obtain ⟨ht0, ht1⟩ := ht
  constructor
  · nlinarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 1 - t0)]
  · nlinarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 1 - t0),
      mul_le_one₀ hs1 (by linarith : (0:ℝ) ≤ 1 - t0) (by linarith)]

lemma firstPartial_mem_edgeSeg (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    firstPartial P y i s ∈ P.edgeSeg i := by
  obtain ⟨hl, hr⟩ := firstPartial_arg_mem P y i hsp hs
  have ht := crossParam_mem_Ioo P y i (Or.inl hsp)
  exact edgeParam_mem_edgeSeg P i ⟨le_trans (le_of_lt ht.1) hl, hr⟩

lemma firstPartial_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    y ≤ (firstPartial P y i s).2 := by
  obtain ⟨hl, hr⟩ := firstPartial_arg_mem P y i hsp hs
  exact edgeParam_above_up P y i hsp hl hr

/-- **Up-edge partial arc is strictly above `y` on the open interval.** For an
up-spanning edge `i`, every interior value `s ∈ (0,1)` of `firstPartial` has height
*strictly* above `y`. (At `s = 0` it equals the crossing point, height `= y`.) This is
the first half of "the crossing arc meets the line `{·.2 = y}` only at its endpoints". -/
lemma firstPartial_gt_y_of_pos (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : y < (firstPartial P y i s).2 := by
  have hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by
    intro h; linarith [hsp.1, hsp.2]
  have ht : 0 < crossParamT P y i ∧ crossParamT P y i < 1 :=
    crossParam_mem_Ioo P y i (Or.inl hsp)
  set t0 := crossParamT P y i with ht0def
  -- firstPartial s = edgeParam i (t0 + s*(1-t0))
  show y < (edgeParam P i (t0 + s * (1 - t0))).2
  have harg0 : t0 < t0 + s * (1 - t0) := by
    have : 0 < s * (1 - t0) := mul_pos hs0 (by linarith [ht.2])
    linarith
  have harg1 : t0 + s * (1 - t0) < 1 := by
    nlinarith [ht.1, ht.2, mul_pos hs0 (show (0:ℝ) < 1 - t0 by linarith [ht.2])]
  have hcross : (edgeParam P i t0).2 = y := by
    rw [ht0def]
    show (edgeParam P i ((y - (toReal (P.vert i)).2) /
      ((toReal (P.vert (i+1))).2 - (toReal (P.vert i)).2))).2 = y
    rw [edgeParam_crossParam P y i hne]
  have hend : y < (edgeParam P i 1).2 := by rw [edgeParam_one]; exact hsp.2
  exact edgeParam_above_strict P y i t0 1 (le_of_eq hcross.symm) (le_of_lt hend)
    (Or.inr hend) harg0 harg1

/-- **Last partial arc.** Reparametrize edge `j` to run from vertex `vⱼ` (at param `0`)
down to the crossing point `(edgeThr y j, y)` (at param `t*`), over `[0,1]`. Used at the
bottom of a down-spanning edge. -/
noncomputable def lastPartial (P : LatticePolygon) (y : ℝ) (j : ZMod P.n) (s : ℝ) : ℝ × ℝ :=
  edgeParam P j (s * crossParamT P y j)

lemma lastPartial_continuous (P : LatticePolygon) (y : ℝ) (j : ZMod P.n) :
    Continuous (lastPartial P y j) := by
  unfold lastPartial
  exact (edgeParam_continuous P j).comp (by fun_prop)

lemma lastPartial_zero (P : LatticePolygon) (y : ℝ) (j : ZMod P.n) :
    lastPartial P y j 0 = toReal (P.vert j) := by
  unfold lastPartial
  rw [show (0:ℝ) * crossParamT P y j = 0 by ring]
  exact edgeParam_zero P j

lemma lastPartial_one (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hne : (toReal (P.vert (j+1))).2 ≠ (toReal (P.vert j)).2) :
    lastPartial P y j 1 = (P.edgeThr y j, y) := by
  unfold lastPartial crossParamT
  rw [show (1:ℝ) * ((y - (toReal (P.vert j)).2) /
      ((toReal (P.vert (j+1))).2 - (toReal (P.vert j)).2))
      = (y - (toReal (P.vert j)).2) /
        ((toReal (P.vert (j+1))).2 - (toReal (P.vert j)).2) by ring]
  exact edgeParam_crossParam P y j hne

/-- For a down-spanning edge `j`, the reparam argument `s·t*` lies in `[0,t*] ⊆ [0,1]`. -/
lemma lastPartial_arg_mem (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ s * crossParamT P y j ∧ s * crossParamT P y j ≤ crossParamT P y j := by
  obtain ⟨hs0, hs1⟩ := hs
  have ht := crossParam_mem_Ioo P y j (Or.inr hsp)
  rw [show crossParamT P y j =
      (y - (toReal (P.vert j)).2) / ((toReal (P.vert (j+1))).2 - (toReal (P.vert j)).2) from rfl]
  set t0 := (y - (toReal (P.vert j)).2) / ((toReal (P.vert (j+1))).2 - (toReal (P.vert j)).2)
  obtain ⟨ht0, ht1⟩ := ht
  exact ⟨mul_nonneg hs0 (le_of_lt ht0),
    by nlinarith [mul_le_of_le_one_left (le_of_lt ht0) hs1]⟩

lemma lastPartial_mem_edgeSeg (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    lastPartial P y j s ∈ P.edgeSeg j := by
  obtain ⟨hl, hr⟩ := lastPartial_arg_mem P y j hsp hs
  have ht := crossParam_mem_Ioo P y j (Or.inr hsp)
  exact edgeParam_mem_edgeSeg P j ⟨hl, le_trans hr (le_of_lt ht.2)⟩

/-- **The up-edge partial arc lies on the first arc chord.** `firstPartial` reparametrizes
edge `i` from its crossing point `(edgeThr y i, y)` (at `s = 0`) up to `vᵢ₊₁` (at `s = 1`),
so every value `firstPartial P y i s` (`s ∈ [0,1]`) lies on the chord
`segment (edgeThr y i, y) vᵢ₊₁` — the first edge of `arcCorners`. Combined with
`firstChord_cross_x`, this locates the first chord's crossing column at any height. -/
lemma firstPartial_mem_chord (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    firstPartial P y i s ∈ segment ℝ ((P.edgeThr y i, y) : ℝ × ℝ) (toReal (P.vert (i + 1))) := by
  have hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by
    intro h; linarith [hsp.1, hsp.2]
  obtain ⟨hs0, hs1⟩ := hs
  set t0 := crossParamT P y i with ht0
  have hpt0 : edgeParam P i t0 = (P.edgeThr y i, y) := by
    rw [ht0]; exact edgeParam_crossParam P y i hne
  have hpt1 : edgeParam P i 1 = toReal (P.vert (i + 1)) := edgeParam_one P i
  show edgeParam P i (t0 + s * (1 - t0)) ∈ _
  rw [segment_eq_image]
  refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
  rw [← hpt0, ← hpt1]
  simp only [edgeParam, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

/-- **The down-edge partial arc lies on the last arc chord.** `lastPartial` reparametrizes
edge `j` from `vⱼ` (at `s = 0`) down to its crossing point `(edgeThr y j, y)` (at `s = 1`),
so every value `lastPartial P y j s` (`s ∈ [0,1]`) lies on the chord
`segment vⱼ (edgeThr y j, y)` — the last edge of `arcCorners` (for `j = i+d`). Combined with
`lastChord_cross_x`, this locates the last chord's crossing column at any height. -/
lemma lastPartial_mem_chord (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    lastPartial P y j s ∈ segment ℝ (toReal (P.vert j)) ((P.edgeThr y j, y) : ℝ × ℝ) := by
  have hne : (toReal (P.vert (j+1))).2 ≠ (toReal (P.vert j)).2 := by
    intro h; linarith [hsp.1, hsp.2]
  obtain ⟨hs0, hs1⟩ := hs
  set t0 := crossParamT P y j with ht0
  have hpt0 : edgeParam P j 0 = toReal (P.vert j) := edgeParam_zero P j
  have hpt1 : edgeParam P j t0 = (P.edgeThr y j, y) := by
    rw [ht0]; exact edgeParam_crossParam P y j hne
  show edgeParam P j (s * t0) ∈ _
  rw [segment_eq_image]
  refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
  rw [← hpt0, ← hpt1]
  simp only [edgeParam, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

lemma lastPartial_above (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    y ≤ (lastPartial P y j s).2 := by
  obtain ⟨hl, hr⟩ := lastPartial_arg_mem P y j hsp hs
  exact edgeParam_above_down P y j hsp hl hr

/-- **Down-edge partial arc is strictly above `y` on the open interval.** For a
down-spanning edge `j`, every interior value `s ∈ (0,1)` of `lastPartial` has height
*strictly* above `y`. (At `s = 1` it equals the crossing point, height `= y`.) Second
half of "the crossing arc meets the line `{·.2 = y}` only at its two endpoints". -/
lemma lastPartial_gt_y_of_pos (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : y < (lastPartial P y j s).2 := by
  have hne : (toReal (P.vert (j+1))).2 ≠ (toReal (P.vert j)).2 := by
    intro h; linarith [hsp.1, hsp.2]
  have ht : 0 < crossParamT P y j ∧ crossParamT P y j < 1 :=
    crossParam_mem_Ioo P y j (Or.inr hsp)
  set t0 := crossParamT P y j with ht0def
  -- lastPartial s = edgeParam j (s * t0)
  show y < (edgeParam P j (s * t0)).2
  have harg0 : (0:ℝ) < s * t0 := mul_pos hs0 ht.1
  have harg1 : s * t0 < t0 := by
    nlinarith [ht.1, mul_lt_of_lt_one_left ht.1 hs1]
  have hstart : y < (edgeParam P j 0).2 := by rw [edgeParam_zero]; exact hsp.2
  have hcross : (edgeParam P j t0).2 = y := by
    rw [ht0def]
    show (edgeParam P j ((y - (toReal (P.vert j)).2) /
      ((toReal (P.vert (j+1))).2 - (toReal (P.vert j)).2))).2 = y
    rw [edgeParam_crossParam P y j hne]
  exact edgeParam_above_strict P y j 0 t0 (le_of_lt hstart) (le_of_eq hcross.symm)
    (Or.inl hstart) harg0 harg1

/-- **The crossing-to-crossing boundary arc.** Starting at the crossing point of edge
`i` (an up-edge), traverse up edge `i` to vertex `vᵢ₊₁`, then run along edges
`i+1, …, i+d−1`, then descend edge `i+d` (a down-edge) to its crossing point. A single
continuous `[0,1]` parametrization from `(edgeThr y i, y)` to `(edgeThr y (i+d), y)`. -/
noncomputable def crossArc (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) : ℝ → ℝ × ℝ :=
  gluePath (firstPartial P y i)
    (gluePath (runParam P (i + 1) (d - 1)) (lastPartial P y (i + (d : ZMod P.n))))

lemma crossArc_continuous (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d) :
    Continuous (crossArc P y i d) := by
  unfold crossArc
  refine gluePath_continuous (firstPartial_continuous P y i)
    (gluePath_continuous (runParam_continuous P (i+1) (d-1))
      (lastPartial_continuous P y (i + (d : ZMod P.n))) ?_) ?_
  · rw [runParam_one_pt, lastPartial_zero]
    congr 2
    have : ((d - 1 : ℕ) : ZMod P.n) + 1 = (d : ZMod P.n) := by
      have : (d - 1 : ℕ) + 1 = d := by omega
      rw [← this]; push_cast; ring
    rw [show i + 1 + ((d - 1 : ℕ) : ZMod P.n) = i + (((d - 1 : ℕ) : ZMod P.n) + 1) by ring, this]
  · rw [firstPartial_one, gluePath_zero, runParam_zero_pt]

lemma crossArc_zero (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2) :
    crossArc P y i d 0 = (P.edgeThr y i, y) := by
  unfold crossArc
  rw [gluePath_zero, firstPartial_zero P y i hne]

lemma crossArc_one (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hne : (toReal (P.vert ((i + (d : ZMod P.n))+1))).2 ≠ (toReal (P.vert (i + (d : ZMod P.n)))).2) :
    crossArc P y i d 1 = (P.edgeThr y (i + (d : ZMod P.n)), y) := by
  unfold crossArc
  rw [gluePath_one, gluePath_one, lastPartial_one P y (i + (d : ZMod P.n)) hne]

/-- **The crossing arc stays weakly above `y`.** Given the up-edge `i` and down-edge
`i+d` spanning, and all vertices `vᵢ, …, vᵢ₊d` weakly above `y`, every value of
`crossArc` has height `≥ y`. -/
lemma crossArc_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hvert : ∀ k : ℕ, k ≤ d → y ≤ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    y ≤ (crossArc P y i d t).2 := by
  unfold crossArc
  -- run-arc above bound
  have hrun : ∀ {s : ℝ}, s ∈ Set.Icc (0:ℝ) 1 → y ≤ (runParam P (i+1) (d-1) s).2 := by
    intro s hs
    refine runParam_above P y (i+1) (d-1) ?_ ?_ hs
    · have := hvert 1 (by omega); simpa using this
    · intro k hk
      have hk' : (k + 1 + 1) ≤ d := by omega
      have := hvert (k + 1 + 1) hk'
      rw [show i + 1 + (k : ZMod P.n) + 1 = i + ((k + 1 + 1 : ℕ) : ZMod P.n) by push_cast; ring]
      exact this
  rcases gluePath_mem_range (f := firstPartial P y i)
      (g := gluePath (runParam P (i+1) (d-1)) (lastPartial P y (i + (d : ZMod P.n)))) ht
      with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
  · rw [heq]; exact firstPartial_above P y i hspi hs
  · rw [heq]
    rcases gluePath_mem_range (f := runParam P (i+1) (d-1))
        (g := lastPartial P y (i + (d : ZMod P.n))) hs with ⟨u, hu, heq2⟩ | ⟨u, hu, heq2⟩
    · rw [heq2]; exact hrun hu
    · rw [heq2]; exact lastPartial_above P y (i + (d : ZMod P.n)) hspj hu

/-- **Every value of the crossing arc lies on one of its edges.** For `t ∈ [0,1]`,
`crossArc P y i d t` belongs to `edgeSeg (i+k)` for some `k ≤ d`. The range-tracking
lemma used to confront the arc with a separate edge via `IsSimple` disjointness. -/
lemma crossArc_mem (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ k : ℕ, k ≤ d ∧ crossArc P y i d t ∈ P.edgeSeg (i + (k : ZMod P.n)) := by
  unfold crossArc
  rcases gluePath_mem_range (f := firstPartial P y i)
      (g := gluePath (runParam P (i+1) (d-1)) (lastPartial P y (i + (d : ZMod P.n)))) ht
      with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
  · refine ⟨0, by omega, ?_⟩
    rw [heq, show i + ((0:ℕ) : ZMod P.n) = i by simp]
    exact firstPartial_mem_edgeSeg P y i hspi hs
  · rw [heq]
    rcases gluePath_mem_range (f := runParam P (i+1) (d-1))
        (g := lastPartial P y (i + (d : ZMod P.n))) hs with ⟨u, hu, heq2⟩ | ⟨u, hu, heq2⟩
    · rw [heq2]
      rcases runParam_mem_edges P (i+1) (d-1) hu with hv | ⟨k, hk, hmem⟩
      · -- equals vert (i+1), an endpoint of edgeSeg (i+1)
        refine ⟨1, by omega, ?_⟩
        rw [hv, show (i + ((1:ℕ) : ZMod P.n)) = (i + 1) by push_cast; ring,
          ← edgeParam_zero P (i+1)]
        exact edgeParam_mem_edgeSeg P (i+1) ⟨le_refl 0, by norm_num⟩
      · refine ⟨k + 1, by omega, ?_⟩
        rw [show i + ((k + 1 : ℕ) : ZMod P.n) = i + 1 + (k : ZMod P.n) by push_cast; ring]
        exact hmem
    · rw [heq2]
      exact ⟨d, le_refl d, lastPartial_mem_edgeSeg P y (i + (d : ZMod P.n)) hspj hu⟩

/-- **The crossing arc meets the line `{·.2 = y}` only at its two endpoints.** Under the
spanning hypotheses (up-edge `i`, down-edge `i+d`) and the genericity that every
intervening vertex `vᵢ₊₁, …, vᵢ₊d` is *strictly* above `y`, every interior point
`t ∈ (0,1)` of `crossArc` has height *strictly* above `y`. Combined with
`crossArc_zero`/`crossArc_one` (the two endpoints are exactly at height `y`), this says
the simple arc `C` touches the horizontal line through its endpoints **only** at those
endpoints — the analytic non-recrossing fact at the heart of the Jordan separation for
`C = crossArc ++ {y}-segment`. -/
lemma crossArc_meets_y_only_endpoints (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hvert : ∀ k : ℕ, 1 ≤ k → k ≤ d → y < (toReal (P.vert (i + (k : ZMod P.n)))).2)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : y < (crossArc P y i d t).2 := by
  -- strict slab bound for the middle run arc (all its endpoints are strictly above y)
  have hrun : ∀ {s : ℝ}, s ∈ Set.Icc (0:ℝ) 1 → y < (runParam P (i+1) (d-1) s).2 := by
    intro s hs
    refine runParam_gt_y P y (i+1) (d-1) ?_ ?_ hs
    · have := hvert 1 (by omega) (by omega); simpa using this
    · intro k hk
      have hk' : (k + 1 + 1) ≤ d := by omega
      have := hvert (k + 1 + 1) (by omega) hk'
      rw [show i + 1 + (k : ZMod P.n) + 1 = i + ((k + 1 + 1 : ℕ) : ZMod P.n) by push_cast; ring]
      exact this
  -- seam value: vert (i+1)
  have hseam1 : y < (toReal (P.vert (i + 1))).2 := hspi.2
  show y < (gluePath (firstPartial P y i)
    (gluePath (runParam P (i+1) (d-1)) (lastPartial P y (i + (d : ZMod P.n)))) t).2
  unfold gluePath
  by_cases hc1 : t ≤ (1:ℝ)/2
  · rw [if_pos hc1]
    -- firstPartial (2t), 2t ∈ (0,1]
    rcases eq_or_lt_of_le hc1 with heq | hlt
    · -- t = 1/2, 2t = 1, firstPartial 1 = vert (i+1)
      rw [show 2 * t = 1 by linarith, firstPartial_one]; exact hseam1
    · -- 2t ∈ (0,1) open
      exact firstPartial_gt_y_of_pos P y i hspi (by linarith) (by linarith)
  · rw [if_neg hc1]
    -- u = 2t-1 ∈ (0,1)
    set u := 2 * t - 1 with hudef
    have hu0 : 0 < u := by rw [hudef]; push_neg at hc1; linarith
    have hu1 : u < 1 := by rw [hudef]; linarith
    show y < (gluePath (runParam P (i+1) (d-1)) (lastPartial P y (i + (d : ZMod P.n))) u).2
    unfold gluePath
    by_cases hc2 : u ≤ (1:ℝ)/2
    · rw [if_pos hc2]
      -- runParam (2u), always strictly above
      exact hrun ⟨by linarith, by linarith⟩
    · rw [if_neg hc2]
      -- lastPartial (2u-1), 2u-1 ∈ (0,1) open
      push_neg at hc2
      exact lastPartial_gt_y_of_pos P y (i + (d : ZMod P.n)) hspj (by linarith) (by linarith)

/-- **A vertex-distant edge `j` is disjoint from the whole crossing arc.** If, for every
arc edge `i+k` (`k ≤ d`), the index `j` satisfies the three `IsSimple` non-adjacency
conditions (`j ≠ i+k`, `j+1 ≠ i+k`, `(i+k)+1 ≠ j`), then no value of `crossArc` lies on
`edgeSeg j`. Pure combinatorial consequence of `IsSimple` edge-disjointness (`hP.2.1`):
the arc range is contained in `⋃_{k≤d} edgeSeg (i+k)` (by `crossArc_mem`), each disjoint
from `edgeSeg j`. This is the disjointness an eventual transversal crossing of `j` by the
arc would contradict — the contradiction that forces the Jordan separation. -/
lemma edgeSeg_j_disjoint_arc (P : LatticePolygon) (hP : P.IsSimple)
    (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d) (j : ZMod P.n)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hsep : ∀ k : ℕ, k ≤ d → j ≠ i + (k : ZMod P.n) ∧
      j + 1 ≠ i + (k : ZMod P.n) ∧ (i + (k : ZMod P.n)) + 1 ≠ j)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    crossArc P y i d t ∉ P.edgeSeg j := by
  intro hmem
  obtain ⟨k, hk, hk_mem⟩ := crossArc_mem P y i d hd hspi hspj ht
  obtain ⟨hne, hne1, hne2⟩ := hsep k hk
  -- IsSimple disjointness of edge j and edge (i+k)
  have hdisj : Disjoint (P.edgeSeg j) (P.edgeSeg (i + (k : ZMod P.n))) :=
    hP.2.1 j (i + (k : ZMod P.n)) hne hne1 hne2
  exact (Set.disjoint_left.mp hdisj hmem) hk_mem

/-- **The crossing arc meets an interposed spanning edge's segment** (under an upper
slab bound). If up-edge `i` and down-edge `i+d` span, all intervening vertices stay
above `y`, an up-spanning edge `j` has its crossing column strictly between the two
arc-endpoint columns, and the arc stays below the top of `j`, then some value of
`crossArc` lies on `edgeSeg j`. This is the transversal-crossing closure feeding the
`IsSimple`-disjointness contradiction of Route B. -/
lemma crossArc_meets_segment (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (j : ZMod P.n)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hvert : ∀ k : ℕ, k ≤ d → y ≤ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2)
    (hbetween : P.edgeThr y i < P.edgeThr y j ∧
      P.edgeThr y j < P.edgeThr y (i + (d : ZMod P.n)))
    (hub : ∀ t ∈ Set.Icc (0:ℝ) 1, (crossArc P y i d t).2 ≤ (toReal (P.vert (j + 1))).2) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, crossArc P y i d t ∈ P.edgeSeg j := by
  have hnei : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by
    intro h; linarith [hspi.1, hspi.2]
  have hnej : (toReal (P.vert ((i + (d : ZMod P.n))+1))).2
      ≠ (toReal (P.vert (i + (d : ZMod P.n)))).2 := by
    intro h; linarith [hspj.1, hspj.2]
  -- crossing of `j` is on its segment
  have hcmem : (P.edgeThr y j, y) ∈ segment ℝ (toReal (P.vert j)) (toReal (P.vert (j+1))) :=
    edgeThr_mem_edgeSeg P y j (Or.inl hupj)
  obtain ⟨t, ht, hmem⟩ := path_above_meets_crossing_segment
    (crossArc_continuous P y i d hd) y (P.edgeThr y i) (P.edgeThr y (i + (d : ZMod P.n)))
    (toReal (P.vert j)) (toReal (P.vert (j+1))) hupj.1 hupj.2
    (crossArc_zero P y i d hnei) (crossArc_one P y i d hnej)
    (lt_trans hbetween.1 hbetween.2)
    (fun t ht => crossArc_above P y i d hd hspi hspj hvert ht)
    hub
    (P.edgeThr y j) hbetween.1 hbetween.2 hcmem
  exact ⟨t, ht, by rw [LatticePolygon.edgeSeg]; exact hmem⟩

/-- **The crossing arc meets the *line* of an interposed spanning edge** (no upper
slab bound). Slab-free companion of `crossArc_meets_segment`: if the crossing column
of up-edge `j` lies strictly between the two arc-endpoint columns, the arc meets the
full line through `vⱼ, vⱼ₊₁` — i.e. there is `t` with `cross (vⱼ₊₁ − vⱼ) (arc t − vⱼ) = 0`.
This survives an arc rising above `vⱼ₊₁`; upgrading to a segment crossing is the
remaining (winding/parity) step. -/
lemma crossArc_meets_line (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (j : ZMod P.n)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2)
    (hbetween : P.edgeThr y i < P.edgeThr y j ∧
      P.edgeThr y j < P.edgeThr y (i + (d : ZMod P.n))) :
    ∃ t ∈ Set.Icc (0:ℝ) 1,
      cross (toReal (P.vert (j+1)) - toReal (P.vert j))
        (crossArc P y i d t - toReal (P.vert j)) = 0 := by
  have hnei : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by
    intro h; linarith [hspi.1, hspi.2]
  have hnej : (toReal (P.vert ((i + (d : ZMod P.n))+1))).2
      ≠ (toReal (P.vert (i + (d : ZMod P.n)))).2 := by
    intro h; linarith [hspj.1, hspj.2]
  have hcmem : (P.edgeThr y j, y) ∈ segment ℝ (toReal (P.vert j)) (toReal (P.vert (j+1))) :=
    edgeThr_mem_edgeSeg P y j (Or.inl hupj)
  exact path_meets_crossing_line
    (crossArc_continuous P y i d hd) y (P.edgeThr y i) (P.edgeThr y (i + (d : ZMod P.n)))
    (toReal (P.vert j)) (toReal (P.vert (j+1))) hupj.1 hupj.2
    (crossArc_zero P y i d hnei) (crossArc_one P y i d hnej)
    (lt_trans hbetween.1 hbetween.2)
    (P.edgeThr y j) hbetween.1 hbetween.2 hcmem

/-! ### STEP D — loop-winding separation to discharge the upper-slab bound `hub`

We form the closed curve `C` = (crossing arc `i → i+d`) followed by the horizontal
return segment from `(edgeThr y (i+d), y)` back to `(edgeThr y i, y)`, and reason
about its winding number `loopWind`.  Every edge of `C` lies (weakly) above height
`y`, so `loopWind q = 0` whenever `q.2 < y`. -/

/-- Winding-number contribution of an **open** polyline `pts` (sum of `edgeWind`
over consecutive vertices). For a list of length `< 2` this is `0`. -/
noncomputable def chainWind : List (ℝ × ℝ) → (ℝ × ℝ) → ℤ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, q => LatticePolygon.edgeWind a b q + chainWind (b :: rest) q

lemma chainWind_nil (q : ℝ × ℝ) : chainWind [] q = 0 := rfl

lemma chainWind_singleton (a q : ℝ × ℝ) : chainWind [a] q = 0 := rfl

lemma chainWind_cons₂ (a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) (q : ℝ × ℝ) :
    chainWind (a :: b :: rest) q
      = LatticePolygon.edgeWind a b q + chainWind (b :: rest) q := rfl

/-- If every vertex of the polyline `pts` has height `≥ y` and `q.2 < y`, then every
edge contributes `0`, so the open polyline contributes `0`. -/
lemma chainWind_eq_zero_of_below {pts : List (ℝ × ℝ)} {q : ℝ × ℝ} {y : ℝ}
    (hq : q.2 < y) (habove : ∀ p ∈ pts, y ≤ p.2) :
    chainWind pts q = 0 := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂]
      have ha : y ≤ a.2 := habove a (by simp)
      have hb : y ≤ b.2 := habove b (by simp)
      rw [edgeWind_eq_zero_of_below a b q (lt_of_lt_of_le hq ha)
        (lt_of_lt_of_le hq hb)]
      rw [zero_add]
      exact ih (fun p hp => habove p (by simp [hp]))

/-- **`chainWind` vanishes when the query is weakly above every vertex.** If every vertex of
the polyline has height `≤ q.2`, the upward ray from `q` cannot meet any edge, so each
`edgeWind` summand is `0` (`edgeWind_eq_zero_of_above`) and the whole open-polyline winding is
`0`. The upper boundary-condition dual of `chainWind_eq_zero_of_below`. -/
lemma chainWind_eq_zero_of_above {pts : List (ℝ × ℝ)} {q : ℝ × ℝ}
    (habove : ∀ p ∈ pts, p.2 ≤ q.2) :
    chainWind pts q = 0 := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂]
      rw [edgeWind_eq_zero_of_above a b q (habove a (by simp)) (habove b (by simp))]
      rw [zero_add]
      exact ih (fun p hp => habove p (by simp [hp]))

/-- If every vertex of the polyline is strictly to the left of `q`, the polyline
contributes `0`. (Companion of `chainWind_eq_zero_of_below`, used for the
right-infinity vanishing in the ray-casting separation argument.) -/
lemma chainWind_eq_zero_of_right {pts : List (ℝ × ℝ)} {q : ℝ × ℝ}
    (hleft : ∀ p ∈ pts, p.1 < q.1) :
    chainWind pts q = 0 := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂]
      rw [edgeWind_eq_zero_of_right a b q (hleft a (by simp)) (hleft b (by simp))]
      rw [zero_add]
      exact ih (fun p hp => hleft p (by simp [hp]))

/-- The ordered list of corners of the crossing arc `i → i+d`:
`(edgeThr y i, y), v_{i+1}, …, v_{i+d}, (edgeThr y (i+d), y)`. -/
noncomputable def arcCorners (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) :
    List (ℝ × ℝ) :=
  (P.edgeThr y i, y) ::
    ((List.range d).map (fun k => toReal (P.vert (i + ((k : ℕ) + 1 : ℕ)))) ++
      [(P.edgeThr y (i + (d : ZMod P.n)), y)])

/-- Winding number of the closed curve `C` = arc `i → i+d` then horizontal return
segment `(edgeThr y (i+d), y) → (edgeThr y i, y)`, around `q`. -/
noncomputable def loopWind (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) : ℤ :=
  chainWind (arcCorners P y i d) q
    + LatticePolygon.edgeWind (P.edgeThr y (i + (d : ZMod P.n)), y) (P.edgeThr y i, y) q

/-- Every corner of the arc has height `≥ y`: the two threshold corners sit exactly
at height `y`, and each interior vertex `v_{i+k}` (`1 ≤ k ≤ d`) is above `y` by
`hvert`. -/
lemma arcCorners_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hvert : ∀ k : ℕ, k ≤ d → y ≤ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (p : ℝ × ℝ) (hp : p ∈ arcCorners P y i d) : y ≤ p.2 := by
  unfold arcCorners at hp
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hp
  rcases hp with hp | ⟨k, hk, rfl⟩ | hp | hp
  · rw [hp]
  · exact hvert (k + 1) (by omega)
  · rw [hp]
  · exact absurd hp (List.not_mem_nil)

/-- A predicate stating that the directed edge `a → b` does not contribute to the
horizontal-step change of the winding around `q`: either it does not span `q`'s
height, or it lies entirely to the left of `q`, or entirely to the right of the
stepped point `q+(1,0)`. -/
def edgeOut (q a b : ℝ × ℝ) : Prop :=
  ((q.2 < a.2 ∧ q.2 < b.2) ∨ (a.2 ≤ q.2 ∧ b.2 ≤ q.2)) ∨
    (a.1 < q.1 ∧ b.1 < q.1) ∨ (q.1 + 1 < a.1 ∧ q.1 + 1 < b.1)

lemma edgeWind_hshift_eq_of_edgeOut (q a b : ℝ × ℝ) (h : edgeOut q a b) :
    edgeWind a b (q + (1, 0)) = edgeWind a b q := by
  have key : edgeWind a b (q + (1, 0)) - edgeWind a b q = 0 := by
    rcases h with hy | hl | hr
    · exact edgeWind_hshift_eq_zero_of_out _ _ q hy
    · exact edgeWind_hshift_eq_zero_of_right _ _ q hl.1 hl.2
    · exact edgeWind_hshift_eq_zero_of_left _ _ q hr.1 hr.2
  linarith

/-- Every consecutive edge of the polyline `pts` is `edgeOut` w.r.t. `q`. A bespoke
recursive predicate, avoiding `List.Chain'` API friction. -/
def chainOut (q : ℝ × ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => edgeOut q a b ∧ chainOut q (b :: rest)

lemma chainOut_cons₂ (q a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    chainOut q (a :: b :: rest) ↔ edgeOut q a b ∧ chainOut q (b :: rest) := Iff.rfl

/-- **Horizontal-step invariance of `chainWind`.** If every consecutive edge of the
polyline is `edgeOut` (does not contribute to the step), then the open-polyline
winding is unchanged by the unit horizontal step. -/
lemma chainWind_hshift_eq_of_chain {pts : List (ℝ × ℝ)} {q : ℝ × ℝ}
    (h : chainOut q pts) :
    chainWind pts (q + (1, 0)) = chainWind pts q := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂, chainWind_cons₂]
      rw [chainOut_cons₂] at h
      rw [edgeWind_hshift_eq_of_edgeOut q a b h.1, ih h.2]

/-- **`loopWind` vanishes strictly below `y`.** All of `C` is at height `≥ y`, so a
query point below `y` is wound `0` times. -/
lemma loopWind_zero_below (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hvert : ∀ k : ℕ, k ≤ d → y ≤ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (q : ℝ × ℝ) (hq : q.2 < y) :
    loopWind P y i d q = 0 := by
  unfold loopWind
  rw [chainWind_eq_zero_of_below hq (arcCorners_above P y i d hvert)]
  rw [edgeWind_eq_zero_of_below _ _ q (by simpa using hq) (by simpa using hq)]
  ring

/-- **`loopWind` vanishes weakly above the whole curve.** If every corner of the arc has
height `≤ q.2` (and `q` is weakly above `y`, so the return segment at height `y` is also below
`q`), then `q` is wound `0` times: the upward ray meets no edge of `C`. The upper-infinity
boundary condition, dual to `loopWind_zero_below`. -/
lemma loopWind_zero_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) (hy : y ≤ q.2) (habove : ∀ p ∈ arcCorners P y i d, p.2 ≤ q.2) :
    loopWind P y i d q = 0 := by
  unfold loopWind
  rw [chainWind_eq_zero_of_above habove]
  rw [edgeWind_eq_zero_of_above _ _ q (by simpa using hy) (by simpa using hy)]
  ring

/-- **`loopWind` vanishes far to the right.** If every corner of the arc (hence both
threshold endpoints of the return segment) lies strictly to the left of `q`, then
`q` is wound `0` times. The right-infinity boundary condition for the ray argument. -/
lemma loopWind_zero_right (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) (hleft : ∀ p ∈ arcCorners P y i d, p.1 < q.1) :
    loopWind P y i d q = 0 := by
  have hthr_i : (P.edgeThr y i, y).1 < q.1 := hleft _ (by
    unfold arcCorners; simp)
  have hthr_j : (P.edgeThr y (i + (d : ZMod P.n)), y).1 < q.1 := hleft _ (by
    unfold arcCorners; simp)
  unfold loopWind
  rw [chainWind_eq_zero_of_right hleft]
  rw [edgeWind_eq_zero_of_right _ _ q hthr_j hthr_i]
  ring

/-- **Horizontal-step invariance of `loopWind`.** If every edge of the closed curve
`C` (the arc edges *and* the return segment) is `edgeOut` w.r.t. `q`, then a unit
horizontal step does not change `loopWind`. This is the local-constancy engine:
along any horizontal segment that meets no edge of `C`, `loopWind` is constant. -/
lemma loopWind_hshift_eq (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ)
    (harc : chainOut q (arcCorners P y i d))
    (hret : edgeOut q (P.edgeThr y (i + (d : ZMod P.n)), y) (P.edgeThr y i, y)) :
    loopWind P y i d (q + (1, 0)) = loopWind P y i d q := by
  unfold loopWind
  rw [chainWind_hshift_eq_of_chain harc,
    edgeWind_hshift_eq_of_edgeOut q _ _ hret]

/-- **The horizontal return segment contributes nothing to `loopWind` above `y`.**
The return segment is horizontal at height `y`; for a query weakly above `y` the
upward ray cannot meet it, so `loopWind` reduces to the open-arc `chainWind`. -/
lemma loopWind_eq_chainWind_of_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) (hq : y ≤ q.2) :
    loopWind P y i d q = chainWind (arcCorners P y i d) q := by
  unfold loopWind
  rw [edgeWind_eq_zero_of_above _ _ q (by simpa using hq) (by simpa using hq), add_zero]

/-- For an up-spanning edge `j` (terminal vertex above `y`), the query point
`vert (j+1)` lies above `y`, so its `loopWind` is the open-arc `chainWind`. The
return segment never affects this query. -/
lemma loopWind_vert_succ_eq_chainWind (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (j : ZMod P.n) (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2) :
    loopWind P y i d (toReal (P.vert (j + 1)))
      = chainWind (arcCorners P y i d) (toReal (P.vert (j + 1))) :=
  loopWind_eq_chainWind_of_above P y i d _ (le_of_lt hupj.2)

/-- The x-coordinates of the arc corners are bounded above: there is `M` strictly
to the right of every corner. The right-infinity boundary for the ray-cast. -/
lemma arcCorners_bddRight (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) :
    ∃ M : ℝ, ∀ p ∈ arcCorners P y i d, p.1 < M := by
  have key : ∀ (L : List (ℝ × ℝ)), ∃ M : ℝ, ∀ p ∈ L, p.1 < M := by
    intro L
    induction L with
    | nil => exact ⟨0, by simp⟩
    | cons a t ih => obtain ⟨M, hM⟩ := ih; exact ⟨max M (a.1 + 1), fun p hp => by
        rcases List.mem_cons.1 hp with rfl | hp
        · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
        · exact lt_of_lt_of_le (hM p hp) (le_max_left _ _)⟩
  exact key _

/-- **`loopWind` vanishes far to the right (explicit bound form).** Once `q.1` is at
least an upper bound `M` of the corner x-coordinates, `q` is wound `0` times. -/
lemma loopWind_zero_far_right (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) (M : ℝ) (hM : ∀ p ∈ arcCorners P y i d, p.1 < M) (hq : M ≤ q.1) :
    loopWind P y i d q = 0 :=
  loopWind_zero_right P y i d q (fun p hp => lt_of_lt_of_le (hM p hp) hq)

/-- **Ray-cast telescoping.** Walking a horizontal ray rightward from `q` by unit
steps, `loopWind` telescopes to a finite sum of per-step jumps; the boundary term at
the far right vanishes by `loopWind_zero_far_right`. So `loopWind q` is exactly the
total signed jump accumulated by the rightward ray. -/
lemma loopWind_eq_ray_sum (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) :
    ∃ N : ℕ, loopWind P y i d q
      = ∑ k ∈ Finset.range N,
          (loopWind P y i d (q.1 + (k:ℝ), q.2)
            - loopWind P y i d (q.1 + ((k:ℝ)+1), q.2)) := by
  classical
  obtain ⟨M, hM⟩ := arcCorners_bddRight P y i d
  obtain ⟨N, hN⟩ := exists_nat_gt (M - q.1)
  refine ⟨N, ?_⟩
  have tele : ∀ m : ℕ, loopWind P y i d (q.1 + (0:ℝ), q.2)
      = (∑ k ∈ Finset.range m,
          (loopWind P y i d (q.1 + (k:ℝ), q.2)
            - loopWind P y i d (q.1 + ((k:ℝ)+1), q.2)))
        + loopWind P y i d (q.1 + (m:ℝ), q.2) := by
    intro m
    induction m with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ]; push_cast at ih ⊢; linarith
  have h0 : loopWind P y i d (q.1 + (0:ℝ), q.2) = loopWind P y i d q := by
    norm_num
  have hlast : loopWind P y i d (q.1 + (N:ℝ), q.2) = 0 := by
    apply loopWind_zero_right
    intro p hp
    have := hM p hp
    simp only []
    linarith [hN]
  rw [h0] at tele
  rw [tele N, hlast, add_zero]

/-- **Ray-cast telescoping in terms of the open arc.** For a query weakly above `y`
the return segment never contributes, so the rightward ray-sum for `loopWind q` is a
telescoping of the open-arc `chainWind` over the horizontal step points. This is the
form fed to the per-edge crossing-jump analysis. -/
lemma loopWind_eq_ray_sum_chainWind (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) (hq : y ≤ q.2) :
    ∃ N : ℕ, loopWind P y i d q
      = ∑ k ∈ Finset.range N,
          (chainWind (arcCorners P y i d) (q.1 + (k:ℝ), q.2)
            - chainWind (arcCorners P y i d) (q.1 + ((k:ℝ)+1), q.2)) := by
  obtain ⟨N, hN⟩ := loopWind_eq_ray_sum P y i d q
  refine ⟨N, ?_⟩
  rw [hN]
  apply Finset.sum_congr rfl
  intro k _
  rw [loopWind_eq_chainWind_of_above P y i d _ (by simpa using hq),
      loopWind_eq_chainWind_of_above P y i d _ (by simpa using hq)]

/-- The per-edge step jump of an open polyline under one horizontal unit step: the
sum over consecutive edges of `edgeWind(q+(1,0)) − edgeWind(q)`. Each summand is `0`
unless the edge spans `q`'s height and its crossing column lies in `(q.1, q.1+1]`
(by `edgeWind_hshift_cross_up`/`_down`). -/
noncomputable def chainStep (q : ℝ × ℝ) : List (ℝ × ℝ) → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
      (LatticePolygon.edgeWind a b (q + (1, 0)) - LatticePolygon.edgeWind a b q)
        + chainStep q (b :: rest)

/-- **A single ray step's `chainWind` jump expands as a per-edge sum.** Reduces the
horizontal-step difference of the polyline winding to `chainStep`, the signed count
of polyline edges whose `y`-span is crossed by the unit step. The atomic engine for
turning the ray-cast telescoping into an edge-crossing count. -/
lemma chainWind_hshift_diff (q : ℝ × ℝ) (pts : List (ℝ × ℝ)) :
    chainWind pts (q + (1, 0)) - chainWind pts q = chainStep q pts := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂, chainWind_cons₂, chainStep]
      rw [← ih]; ring

/-- **`chainStep` vanishes on a `chainOut` polyline.** If every consecutive edge of
`pts` is `edgeOut q` (does not contribute to the horizontal step), then the total
per-edge step `chainStep q pts` is `0`. Immediate from `chainWind_hshift_diff` and
`chainWind_hshift_eq_of_chain`. -/
lemma chainStep_eq_zero_of_chainOut (q : ℝ × ℝ) (pts : List (ℝ × ℝ))
    (h : chainOut q pts) : chainStep q pts = 0 := by
  rw [← chainWind_hshift_diff, chainWind_hshift_eq_of_chain h, sub_self]

/-- **A polyline whose every corner is strictly above the query height is `chainOut`.**
If every point of `pts` has height `> q.2`, then each consecutive edge has both
endpoints strictly above `q`, so it is `edgeOut q` (first disjunct). -/
lemma chainOut_of_all_above (q : ℝ × ℝ) (pts : List (ℝ × ℝ))
    (h : ∀ p ∈ pts, q.2 < p.2) : chainOut q pts := by
  induction pts with
  | nil => exact True.intro
  | cons a rest ih =>
    cases rest with
    | nil => exact True.intro
    | cons b rest' =>
      refine ⟨Or.inl (Or.inl ⟨h a (by simp), h b (by simp)⟩), ?_⟩
      exact ih (fun p hp => h p (by simp [hp]))

/-- **`chainStep` vanishes on a polyline strictly above the query.** Combines
`chainOut_of_all_above` with `chainStep_eq_zero_of_chainOut`: a run arc entirely above
the query height `q.2` contributes nothing to the horizontal-step count. -/
lemma chainStep_eq_zero_of_all_above (q : ℝ × ℝ) (pts : List (ℝ × ℝ))
    (h : ∀ p ∈ pts, q.2 < p.2) : chainStep q pts = 0 :=
  chainStep_eq_zero_of_chainOut q pts (chainOut_of_all_above q pts h)

/-- **`chainStep` telescopes over `append`.** The per-edge step of a concatenated
polyline is the sum of the steps of the two parts plus the single bridging edge between
the last point of `l₁` and the head of `l₂`. The bookkeeping identity for isolating the
contribution of each chord of `arcCorners`. -/
lemma chainStep_append (q : ℝ × ℝ) (l₁ l₂ : List (ℝ × ℝ)) (a : ℝ × ℝ) :
    chainStep q (l₁ ++ a :: l₂)
      = chainStep q (l₁ ++ [a]) + chainStep q (a :: l₂) := by
  induction l₁ with
  | nil => simp [chainStep]
  | cons x rest ih =>
    cases rest with
    | nil => simp [chainStep]
    | cons y rest' =>
      simp only [List.cons_append, chainStep] at ih ⊢
      rw [ih]; ring

/-- **The `cross` value of a query against an edge equals the height-drop times the
horizontal offset of the crossing point.** If `w` lies on segment `[a,b]` at the query
height (`w.2 = q.2`), then `cross (b−a) (q−a) = (b.2−a.2)·(w.1−q.1)`. The sign of the
edge's `cross` (hence its `edgeWind`) is thus governed by whether the crossing column
`w.1` is left or right of the query column `q.1`. -/
lemma cross_eq_height_mul_offset (a b w q : ℝ × ℝ) (hw : w ∈ segment ℝ a b)
    (hwq : w.2 = q.2) :
    cross (b - a) (q - a) = (b.2 - a.2) * (w.1 - q.1) := by
  have hz : cross (b - a) (w - a) = 0 := cross_eq_zero_of_mem_segment a b w hw
  unfold cross at hz ⊢
  simp only [Prod.fst_sub, Prod.snd_sub] at hz ⊢
  rw [hwq] at hz
  nlinarith [hz]

/-- **An up-edge whose crossing column is left of the query contributes `0`.** For an
up-spanning edge `a → b` (`a.2 ≤ q.2 < b.2`) whose crossing point `w` at the query
height has `w.1 < q.1` (the crossing lies strictly left of the query column), the
rightward ray from `q` does not meet the edge, so `edgeWind a b q = 0`. -/
lemma edgeWind_eq_zero_of_up_cross_left (a b w q : ℝ × ℝ)
    (hw : w ∈ segment ℝ a b) (hwq : w.2 = q.2)
    (h1 : a.2 ≤ q.2) (h2 : q.2 < b.2) (hleft : w.1 < q.1) :
    edgeWind a b q = 0 := by
  have hcross : cross (b - a) (q - a) = (b.2 - a.2) * (w.1 - q.1) :=
    cross_eq_height_mul_offset a b w q hw hwq
  rcases edgeWind_mem a b q with h | h | h
  · exact absurd ((edgeWind_eq_neg_one_iff a b q).mp h).2.1 (by linarith)
  · exact h
  · exact absurd ((edgeWind_eq_one_iff a b q).mp h).2.2 (by
      rw [hcross]; nlinarith [sub_pos.mpr h2])

/-- **A down-edge whose crossing column is right of the query contributes `−1`.** For a
down-spanning edge `a → b` (`b.2 ≤ q.2 < a.2`) whose crossing point `w` at the query
height has `q.1 < w.1` (the crossing lies strictly right of the query column), the
rightward ray from `q` meets the edge, giving `edgeWind a b q = −1`. -/
lemma edgeWind_eq_neg_one_of_down_cross_right (a b w q : ℝ × ℝ)
    (hw : w ∈ segment ℝ a b) (hwq : w.2 = q.2)
    (h1 : b.2 ≤ q.2) (h2 : q.2 < a.2) (hright : q.1 < w.1) :
    edgeWind a b q = -1 := by
  have hcross : cross (b - a) (q - a) = (b.2 - a.2) * (w.1 - q.1) :=
    cross_eq_height_mul_offset a b w q hw hwq
  rw [(edgeWind_eq_neg_one_iff a b q).mpr ⟨h1, h2, ?_⟩]
  rw [hcross]
  have hba : b.2 - a.2 < 0 := by linarith
  have hwq' : 0 < w.1 - q.1 := by linarith
  nlinarith

/-- **`chainWind` of a polyline `a :: mid ++ [b]` whose middle is strictly above the
query reduces to its two boundary chords.** If every vertex of the nonempty middle
list `m0 :: mid` has height `> q.2`, then every interior chord (both endpoints above
`q`) contributes `0`, so only the first chord `a → m0` and the last chord
`(last of middle) → b` survive. This is the list-structure backbone of the
`arcCorners` crossing count: the run vertices are all above `y+ε`, so only the two
partial chords matter. -/
lemma chainWind_middle_above (q a b : ℝ × ℝ) (m0 : ℝ × ℝ) (mid : List (ℝ × ℝ))
    (h : ∀ p ∈ (m0 :: mid), q.2 < p.2) :
    chainWind (a :: (m0 :: mid) ++ [b]) q
      = LatticePolygon.edgeWind a m0 q
        + LatticePolygon.edgeWind ((m0 :: mid).getLast (by simp)) b q := by
  induction mid generalizing a m0 with
  | nil => simp [chainWind, chainWind_cons₂]
  | cons x rest ih =>
    have estep : chainWind (a :: (m0 :: x :: rest) ++ [b]) q
        = LatticePolygon.edgeWind a m0 q + chainWind (m0 :: (x :: rest) ++ [b]) q := by
      simp only [List.cons_append, chainWind_cons₂]
    rw [estep]
    have key := ih m0 x (fun p hp => h p (by simp only [List.mem_cons] at hp ⊢; tauto))
    rw [key]
    have hm0 : q.2 < m0.2 := h m0 (by simp)
    have hx : q.2 < x.2 := h x (by simp)
    rw [edgeWind_eq_zero_of_below m0 x q hm0 hx, zero_add]
    congr 2

/-- **`chainWind (a :: L ++ [b])` with `L` nonempty and strictly above the query reduces
to its two boundary chords.** Head/`getLast` packaging of `chainWind_middle_above`: for a
nonempty middle list `L` (all of whose vertices are above `q.2`), only the first chord
`a → L.head` and the last chord `L.getLast → b` survive. The exact shape consumed by the
`arcCorners` crossing count. -/
lemma chainWind_a_cons_L_append (q a b : ℝ × ℝ) (L : List (ℝ × ℝ)) (hL : L ≠ [])
    (h : ∀ p ∈ L, q.2 < p.2) :
    chainWind (a :: L ++ [b]) q
      = LatticePolygon.edgeWind a (L.head hL) q
        + LatticePolygon.edgeWind (L.getLast hL) b q := by
  obtain ⟨m0, mid, rfl⟩ := List.exists_cons_of_ne_nil hL
  rw [chainWind_middle_above q a b m0 mid h, List.head_cons]

/-- **The crossing arc hits every interposed column.** Since `crossArc` is continuous
from `(edgeThr y i, y)` (x-coordinate `edgeThr y i` at param `0`) to
`(edgeThr y (i+d), y)` (x-coordinate `edgeThr y (i+d)` at param `1`), and its
x-coordinate is continuous, by the intermediate value theorem it attains every value
`c` between the two endpoint columns. Pure IVT on the first coordinate — slab-free. -/
lemma crossArc_hits_column (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hnei : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2)
    (hnej : (toReal (P.vert ((i + (d : ZMod P.n))+1))).2
      ≠ (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (c : ℝ) (hcl : P.edgeThr y i ≤ c) (hcr : c ≤ P.edgeThr y (i + (d : ZMod P.n))) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, (crossArc P y i d t).1 = c := by
  have hxcont : Continuous (fun t => (crossArc P y i d t).1) :=
    (continuous_fst.comp (crossArc_continuous P y i d hd))
  have hx0 : (crossArc P y i d 0).1 = P.edgeThr y i := by
    rw [crossArc_zero P y i d hnei]
  have hx1 : (crossArc P y i d 1).1 = P.edgeThr y (i + (d : ZMod P.n)) := by
    rw [crossArc_one P y i d hnej]
  have hmem : c ∈ Set.Icc (crossArc P y i d 0).1 (crossArc P y i d 1).1 := by
    rw [hx0, hx1]; exact ⟨hcl, hcr⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
    hxcont.continuousOn hmem
  exact ⟨t, ht, hft⟩

/-- **The crossing arc hits every interposed column at a point weakly above `y`.**
Combines `crossArc_hits_column` (IVT on the x-coordinate) with `crossArc_above`
(the arc stays weakly above `y`): for any column `c` between the two arc-endpoint
columns there is an arc point `(c, h)` with `h ≥ y`. This is the geometric fact that
the arc, entering and leaving at height `y`, can only reach column `edgeThr y j`
*inside* the closed region bounded below by the line `{y}`. -/
lemma crossArc_hits_column_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hvert : ∀ k : ℕ, k ≤ d → y ≤ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (c : ℝ) (hcl : P.edgeThr y i ≤ c) (hcr : c ≤ P.edgeThr y (i + (d : ZMod P.n))) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, (crossArc P y i d t).1 = c ∧ y ≤ (crossArc P y i d t).2 := by
  have hnei : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by
    intro h; linarith [hspi.1, hspi.2]
  have hnej : (toReal (P.vert ((i + (d : ZMod P.n))+1))).2
      ≠ (toReal (P.vert (i + (d : ZMod P.n)))).2 := by
    intro h; linarith [hspj.1, hspj.2]
  obtain ⟨t, ht, hft⟩ := crossArc_hits_column P y i d hd hnei hnej c hcl hcr
  exact ⟨t, ht, hft, crossArc_above P y i d hd hspi hspj hvert ht⟩

/-- **Edge `j`'s upper part lies on `edgeSeg j`.** The crossing point `(edgeThr y j, y)`
and the above-vertex `vⱼ₊₁` are both points of the convex segment `edgeSeg j` (the first
by `edgeThr_mem_edgeSeg`, the second as an endpoint), so any convex combination
`(1−s)·(edgeThr y j, y) + s·vⱼ₊₁` (`s ∈ [0,1]`) is again on `edgeSeg j`. -/
lemma edge_j_upper_mem_edgeSeg (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) • (P.edgeThr y j, y) + s • (toReal (P.vert (j + 1))) ∈ P.edgeSeg j := by
  have hcross : (P.edgeThr y j, y) ∈ P.edgeSeg j := edgeThr_mem_edgeSeg P y j (Or.inl hupj)
  have hend : toReal (P.vert (j + 1)) ∈ P.edgeSeg j := by
    rw [LatticePolygon.edgeSeg]; exact right_mem_segment ℝ _ _
  rw [LatticePolygon.edgeSeg] at hcross hend ⊢
  exact (convex_segment _ _) hcross hend (by linarith) hs0 (by ring)

/-- **Edge `j`'s upper part is disjoint from the crossing arc.** Combining
`edge_j_upper_mem_edgeSeg` (the upper part lies on `edgeSeg j`) with
`edgeSeg_j_disjoint_arc` (the whole arc misses `edgeSeg j`), no value of `crossArc` equals
a point of edge `j`'s upper part. This is the "edge `j`'s upper part is off the arc edges
of `C`" fact for the local-constancy step. -/
lemma edge_j_upper_notMem_arc (P : LatticePolygon) (hP : P.IsSimple)
    (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d) (j : ZMod P.n)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hsep : ∀ k : ℕ, k ≤ d → j ≠ i + (k : ZMod P.n) ∧
      j + 1 ≠ i + (k : ZMod P.n) ∧ (i + (k : ZMod P.n)) + 1 ≠ j)
    (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    crossArc P y i d t ≠ (1 - s) • (P.edgeThr y j, y) + s • (toReal (P.vert (j + 1))) := by
  intro heq
  have harc_off : crossArc P y i d t ∉ P.edgeSeg j :=
    edgeSeg_j_disjoint_arc P hP y i d hd j hspi hspj hsep ht
  exact harc_off (heq ▸ edge_j_upper_mem_edgeSeg P y j hupj hs0 hs1)

/-- **The horizontal return segment of `C` is `edgeOut` for any query strictly above
`y`.** The return segment runs from `(edgeThr y (i+d), y)` to `(edgeThr y i, y)`, both at
height exactly `y`. For a query `q` with `q.2 > y` the segment lies entirely below `q`'s
height (`a.2 = b.2 = y < q.2`), so it is in the first `edgeOut` disjunct and a unit
horizontal step never crosses it. This discharges the `hret` hypothesis of
`loopWind_hshift_eq` uniformly along any horizontal motion above `y`. -/
lemma return_edgeOut_of_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q : ℝ × ℝ) (hq : y < q.2) :
    edgeOut q (P.edgeThr y (i + (d : ZMod P.n)), y) (P.edgeThr y i, y) := by
  exact Or.inl (Or.inr ⟨le_of_lt hq, le_of_lt hq⟩)

/-- **Edge `j`'s upper part stays strictly above `y`.** For an up-spanning edge `j`
(`vⱼ` below, `vⱼ₊₁` above `y`), the straight segment from its crossing point
`(edgeThr y j, y)` (at height exactly `y`) to the above-vertex `vⱼ₊₁` has every point
`(1−s)·(edgeThr y j, y) + s·vⱼ₊₁` with `s ∈ (0,1]` strictly above `y`. The height is a
convex combination `(1−s)·y + s·(vⱼ₊₁).2`, and `(vⱼ₊₁).2 > y` with `s > 0`. This is the
"upper part of edge `j` lies off the horizontal return segment of `C`" fact for the
local-constancy step. -/
lemma edge_j_upper_above_y (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    y < ((1 - s) • (P.edgeThr y j, y) + s • (toReal (P.vert (j + 1)))).2 := by
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hb : y < (toReal (P.vert (j + 1))).2 := hupj.2
  nlinarith [mul_pos hs0 (sub_pos.mpr hb)]

/-- **Edge `j`'s upper part is off the horizontal return segment of `C`.** The return
segment is `segment ℝ (edgeThr y (i+d), y) (edgeThr y i, y)`, all at height exactly `y`.
A point of edge `j`'s upper part with `s ∈ (0,1]` has height strictly above `y`
(`edge_j_upper_above_y`), hence cannot lie on the return segment, whose points all have
height `y`. Together with `edge_j_upper_notMem_arc` this shows edge `j`'s upper part is
entirely off the closed curve `C`. -/
lemma edge_j_upper_notMem_return (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (j : ZMod P.n)
    (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (1 - s) • (P.edgeThr y j, y) + s • (toReal (P.vert (j + 1)))
      ∉ segment ℝ ((P.edgeThr y (i + (d : ZMod P.n)), y) : ℝ × ℝ) (P.edgeThr y i, y) := by
  intro hmem
  rw [segment_eq_image] at hmem
  obtain ⟨r, _, hr⟩ := hmem
  -- every point of the return segment has height exactly y
  have hheight : ((1 - s) • (P.edgeThr y j, y) + s • (toReal (P.vert (j + 1)))).2 = y := by
    rw [← hr]; simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
  exact absurd hheight (ne_of_gt (edge_j_upper_above_y P y j hupj hs0 hs1))

/-- **Edge `j`'s upper part is entirely off the closed curve `C`.** A point
`P_s = (1−s)·(edgeThr y j, y) + s·vⱼ₊₁` of edge `j`'s upper part with `s ∈ (0,1]` is on
neither an arc edge of `C` (it lies on `edgeSeg j`, disjoint from the arc by
`edge_j_upper_notMem_arc`) nor the horizontal return segment (it is strictly above `y`,
by `edge_j_upper_notMem_return`). Packaged as the "`P_s ∉ C`" hypothesis for the
local-constancy of `loopWind` along edge `j`'s upper part. -/
lemma edge_j_upper_off_C (P : LatticePolygon) (hP : P.IsSimple)
    (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d) (j : ZMod P.n)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hsep : ∀ k : ℕ, k ≤ d → j ≠ i + (k : ZMod P.n) ∧
      j + 1 ≠ i + (k : ZMod P.n) ∧ (i + (k : ZMod P.n)) + 1 ≠ j)
    (hupj : (toReal (P.vert j)).2 < y ∧ y < (toReal (P.vert (j + 1))).2)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∀ t ∈ Set.Icc (0:ℝ) 1,
        crossArc P y i d t ≠ (1 - s) • (P.edgeThr y j, y) + s • (toReal (P.vert (j + 1)))) ∧
      (1 - s) • (P.edgeThr y j, y) + s • (toReal (P.vert (j + 1)))
        ∉ segment ℝ ((P.edgeThr y (i + (d : ZMod P.n)), y) : ℝ × ℝ) (P.edgeThr y i, y) := by
  refine ⟨fun t ht => ?_, edge_j_upper_notMem_return P y i d j hupj hs0 hs1⟩
  exact edge_j_upper_notMem_arc P hP y i d hd j hspi hspj hsep hupj (le_of_lt hs0) hs1 ht

/-- **The middle run arc of `crossArc` stays uniformly above `y` by a margin `ε > 0`.**
The run arc `runParam P (i+1) (d-1)` is continuous on the compact interval `[0,1]` and,
under the genericity hypothesis that every intervening vertex `vᵢ₊₁, …, vᵢ₊d` is *strictly*
above `y`, every point has height `> y` (`runParam_gt_y` via `crossArc_meets_y_only_endpoints`
plumbing). By compactness the height attains a minimum, which is `> y`; half the gap is the
desired `ε`. This is the local-ε existence underlying "for `ε` small enough, the only `C`-edges
meeting height `y+ε` are `firstPartial`/`lastPartial`". -/
lemma run_edges_above_eps (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hvert : ∀ k : ℕ, 1 ≤ k → k ≤ d → y < (toReal (P.vert (i + (k : ZMod P.n)))).2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Icc (0:ℝ) 1, y + ε < (runParam P (i+1) (d-1) s).2 := by
  -- strict slab bound for the middle run arc (all its endpoints are strictly above y)
  have hrun : ∀ s ∈ Set.Icc (0:ℝ) 1, y < (runParam P (i+1) (d-1) s).2 := by
    intro s hs
    refine runParam_gt_y P y (i+1) (d-1) ?_ ?_ hs
    · have := hvert 1 (by omega) (by omega); simpa using this
    · intro k hk
      have hk' : (k + 1 + 1) ≤ d := by omega
      have := hvert (k + 1 + 1) (by omega) hk'
      rw [show i + 1 + (k : ZMod P.n) + 1 = i + ((k + 1 + 1 : ℕ) : ZMod P.n) by push_cast; ring]
      exact this
  -- height function is continuous on the compact [0,1]; take its minimum
  have hcont : ContinuousOn (fun s => (runParam P (i+1) (d-1) s).2) (Set.Icc (0:ℝ) 1) :=
    (continuous_snd.comp (runParam_continuous P (i+1) (d-1))).continuousOn
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (0:ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨s₀, hs₀mem, hs₀min⟩ := hcompact.exists_isMinOn hne hcont
  refine ⟨((runParam P (i+1) (d-1) s₀).2 - y) / 2, by
    have := hrun s₀ hs₀mem; linarith, ?_⟩
  intro s hs
  have hge : (runParam P (i+1) (d-1) s₀).2 ≤ (runParam P (i+1) (d-1) s).2 := hs₀min hs
  have := hrun s₀ hs₀mem
  linarith

/-- **A uniform small margin `ε` isolating the two partial edges.** Strengthens
`run_edges_above_eps`: there is a single `ε > 0` such that the middle run arc stays above
`y+ε` *and* `y+ε` is strictly below both above-vertices `vᵢ₊₁` and `vᵢ₊d`. At this height,
`firstPartial` and `lastPartial` each cross `y+ε` (by `firstPartial_hits_eps`/
`lastPartial_hits_eps`) while the run arc does not, and the horizontal return segment (height
`y`) does not. So height `y+ε` meets `C` only on the two partial edges — the geometric
setup for the ray-sum count in `loopWind_just_above_segment`. -/
lemma run_partials_eps (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hvert : ∀ k : ℕ, 1 ≤ k → k ≤ d → y < (toReal (P.vert (i + (k : ZMod P.n)))).2) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ s ∈ Set.Icc (0:ℝ) 1, y + ε < (runParam P (i+1) (d-1) s).2) ∧
      y + ε < (toReal (P.vert (i + 1))).2 ∧
      y + ε < (toReal (P.vert (i + (d : ZMod P.n)))).2 := by
  obtain ⟨ε₀, hε₀pos, hrun⟩ := run_edges_above_eps P y i d hd hspi hvert
  -- shrink ε₀ so it also lies below both above-vertices
  set g₁ := (toReal (P.vert (i + 1))).2 - y with hg₁
  set g₂ := (toReal (P.vert (i + (d : ZMod P.n)))).2 - y with hg₂
  have hg₁pos : 0 < g₁ := by rw [hg₁]; linarith [hspi.2]
  have hg₂pos : 0 < g₂ := by rw [hg₂]; linarith [hspj.2]
  set ε := min ε₀ (min (g₁/2) (g₂/2)) with hε
  have hεpos : 0 < ε := by
    rw [hε]; exact lt_min hε₀pos (lt_min (by linarith) (by linarith))
  have hle0 : ε ≤ ε₀ := by rw [hε]; exact min_le_left _ _
  have hle1 : ε ≤ g₁/2 := le_trans (by rw [hε]; exact min_le_right _ _) (min_le_left _ _)
  have hle2 : ε ≤ g₂/2 := le_trans (by rw [hε]; exact min_le_right _ _) (min_le_right _ _)
  refine ⟨ε, hεpos, ?_, ?_, ?_⟩
  · intro s hs; have := hrun s hs; linarith
  · have : y + ε ≤ y + g₁/2 := by linarith
    rw [hg₁] at this; linarith
  · have : y + ε ≤ y + g₂/2 := by linarith
    rw [hg₂] at this; linarith

/-- **The up-edge partial arc attains every height in `(y, vᵢ₊₁.2)`.** `firstPartial`
runs continuously from `(edgeThr y i, y)` (height exactly `y`, at `s = 0`) up to the
above-vertex `vᵢ₊₁` (height `> y`, at `s = 1`). By the intermediate value theorem, for any
target height `h` with `y < h < vᵢ₊₁.2` there is an interior parameter `s ∈ (0,1)` with
`(firstPartial s).2 = h`. The "`firstPartial` crosses height `y+ε`" existence used in the
ray-sum analysis. -/
lemma firstPartial_hits_eps (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {h : ℝ} (hh0 : y < h) (hh1 : h < (toReal (P.vert (i + 1))).2) :
    ∃ s ∈ Set.Ioo (0:ℝ) 1, (firstPartial P y i s).2 = h := by
  have hne : (toReal (P.vert (i+1))).2 ≠ (toReal (P.vert i)).2 := by
    intro hcon; linarith [hsp.1, hsp.2]
  have hcont : Continuous (fun s => (firstPartial P y i s).2) :=
    continuous_snd.comp (firstPartial_continuous P y i)
  have h0 : (firstPartial P y i 0).2 = y := by
    rw [firstPartial_zero P y i hne]
  have h1 : (firstPartial P y i 1).2 = (toReal (P.vert (i + 1))).2 := by
    rw [firstPartial_one]
  have hmem : h ∈ Set.Icc (firstPartial P y i 0).2 (firstPartial P y i 1).2 := by
    rw [h0, h1]; exact ⟨le_of_lt hh0, le_of_lt hh1⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
    hcont.continuousOn hmem
  simp only [] at hfs
  refine ⟨s, ⟨?_, ?_⟩, hfs⟩
  · rcases eq_or_lt_of_le hs.1 with heq | hlt
    · exfalso; rw [← heq, h0] at hfs; linarith
    · exact hlt
  · rcases eq_or_lt_of_le hs.2 with heq | hlt
    · exfalso; rw [heq, h1] at hfs; linarith
    · exact hlt

/-- **The down-edge partial arc attains every height in `(y, vⱼ.2)`.** `lastPartial`
runs continuously from the above-vertex `vⱼ` (height `> y`, at `s = 0`) down to its crossing
point `(edgeThr y j, y)` (height exactly `y`, at `s = 1`). By the intermediate value theorem,
for any target height `h` with `y < h < vⱼ.2` there is an interior parameter `s ∈ (0,1)` with
`(lastPartial s).2 = h`. The "`lastPartial` crosses height `y+ε`" existence used in the
ray-sum analysis. -/
lemma lastPartial_hits_eps (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {h : ℝ} (hh0 : y < h) (hh1 : h < (toReal (P.vert j)).2) :
    ∃ s ∈ Set.Ioo (0:ℝ) 1, (lastPartial P y j s).2 = h := by
  have hne : (toReal (P.vert (j+1))).2 ≠ (toReal (P.vert j)).2 := by
    intro hcon; linarith [hsp.1, hsp.2]
  have hcont : Continuous (fun s => (lastPartial P y j s).2) :=
    continuous_snd.comp (lastPartial_continuous P y j)
  have h0 : (lastPartial P y j 0).2 = (toReal (P.vert j)).2 := by
    rw [lastPartial_zero]
  have h1 : (lastPartial P y j 1).2 = y := by
    rw [lastPartial_one P y j hne]
  have hmem : h ∈ Set.Icc (lastPartial P y j 1).2 (lastPartial P y j 0).2 := by
    rw [h0, h1]; exact ⟨le_of_lt hh0, le_of_lt hh1⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1)
    hcont.continuousOn hmem
  simp only [] at hfs
  refine ⟨s, ⟨?_, ?_⟩, hfs⟩
  · rcases eq_or_lt_of_le hs.1 with heq | hlt
    · exfalso; rw [← heq, h0] at hfs; linarith
    · exact hlt
  · rcases eq_or_lt_of_le hs.2 with heq | hlt
    · exfalso; rw [heq, h1] at hfs; linarith
    · exact hlt

/-- **The first spanning edge after a spanning edge has the opposite sign.** Given a
spanning edge `i` and any later spanning edge `i + D` (`D ≥ 1`), there is a *first*
spanning edge `i + d` (`1 ≤ d ≤ D`, no spanning edge strictly between in vertex order)
whose `edgeSign` differs from that of `i`. Packages the combinatorial extraction
`next_spanning_exists` with the sign-flip `edgeSign_ne_of_consecutive_spanning`. This
is the vertex-consecutive base case feeding the threshold-adjacency reduction. -/
lemma first_spanning_after_opposite (P : LatticePolygon) (y : ℝ)
    (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) (D : ℕ) (hD : 1 ≤ D)
    (hspi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    (hspD : (((toReal (P.vert (i + D))).2 < y ∧ y < (toReal (P.vert (i + D + 1))).2) ∨
      ((toReal (P.vert (i + D + 1))).2 < y ∧ y < (toReal (P.vert (i + D))).2))) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧
      (((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2) ∨
        ((toReal (P.vert (i + d + 1))).2 < y ∧ y < (toReal (P.vert (i + d))).2)) ∧
      P.edgeSign y i ≠ P.edgeSign y (i + d) := by
  obtain ⟨d, hd1, hdD, hdsp, hdmid⟩ := next_spanning_exists P y i D hD hspD
  refine ⟨d, hd1, hdD, hdsp, ?_⟩
  exact edgeSign_ne_of_consecutive_spanning P y hy i d hd1 hspi hdsp hdmid

/-- **`edgeThr` is continuous in the height argument.** For an edge `i` whose endpoints
have distinct heights (`v_{i+1}.2 ≠ v_i.2`), `edgeThr · i` is the affine-in-`y`
expression `crossThreshold a b y`, hence continuous as a function of the height. The
limiting fact behind the column-control of the partial-edge crossings as `ε → 0`. -/
lemma edgeThr_continuous (P : LatticePolygon) (i : ZMod P.n)
    (hne : (toReal (P.vert (i + 1))).2 ≠ (toReal (P.vert i)).2) :
    Continuous (fun y => P.edgeThr y i) := by
  unfold LatticePolygon.edgeThr crossThreshold
  have hd : (toReal (P.vert (i + 1))).2 - (toReal (P.vert i)).2 ≠ 0 := sub_ne_zero.mpr hne
  fun_prop (disch := assumption)

/-- **`firstPartial`'s crossing point at height `h` lies at column `edgeThr h i`.** If
the up-spanning edge `i` (`v_i.2 < y < v_{i+1}.2`) is reparametrized by `firstPartial`
and the point `firstPartial P y i s` (with `s ∈ [0,1]`) has height `h` with
`y < h < v_{i+1}.2`, then its x-coordinate is exactly `edgeThr h i`. Edge `i` also spans
`h` (since `v_i.2 < y < h`), so the unique point of `edgeSeg i` at height `h` is the
threshold point `(edgeThr h i, h)`. -/
lemma firstPartial_cross_x (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) {h : ℝ}
    (hh0 : y < h) (hh1 : h < (toReal (P.vert (i + 1))).2)
    (hheight : (firstPartial P y i s).2 = h) :
    (firstPartial P y i s).1 = P.edgeThr h i := by
  have hmem : firstPartial P y i s ∈ P.edgeSeg i := firstPartial_mem_edgeSeg P y i hsp hs
  have hspan_h : (toReal (P.vert i)).2 < h ∧ h < (toReal (P.vert (i + 1))).2 :=
    ⟨lt_trans hsp.1 hh0, hh1⟩
  have heq := edgeThr_unique_cross P h i (Or.inl hspan_h) (firstPartial P y i s) hmem hheight
  rw [heq]

/-- **`lastPartial`'s crossing point at height `h` lies at column `edgeThr h j`.**
Companion of `firstPartial_cross_x` for the down-spanning edge `j`
(`v_{j+1}.2 < y < v_j.2`): the point `lastPartial P y j s` (`s ∈ [0,1]`) at height `h`
with `y < h < v_j.2` has x-coordinate exactly `edgeThr h j`. -/
lemma lastPartial_cross_x (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) {h : ℝ}
    (hh0 : y < h) (hh1 : h < (toReal (P.vert j)).2)
    (hheight : (lastPartial P y j s).2 = h) :
    (lastPartial P y j s).1 = P.edgeThr h j := by
  have hmem : lastPartial P y j s ∈ P.edgeSeg j := lastPartial_mem_edgeSeg P y j hsp hs
  have hspan_h : (toReal (P.vert (j + 1))).2 < h ∧ h < (toReal (P.vert j)).2 :=
    ⟨lt_trans hsp.1 hh0, hh1⟩
  have heq := edgeThr_unique_cross P h j (Or.inr hspan_h) (lastPartial P y j s) hmem hheight
  rw [heq]

/-- **Column control as `ε → 0`.** For a column `c` strictly between the two arc-endpoint
thresholds (`edgeThr y i < c < edgeThr y (i+d)`), there is `δ > 0` such that every height
`h` with `|h - y| < δ` keeps `edgeThr h i < c` and `c < edgeThr h (i+d)`. By continuity of
`edgeThr · i` and `edgeThr · (i+d)`, the sets `{h | edgeThr h i < c}` and
`{h | c < edgeThr h (i+d)}` are open neighborhoods of `y`. This is the analytic core: as the
slab height shrinks to `y`, the partial-edge crossing columns stay on the correct side of `c`. -/
lemma edgeThr_column_nhds (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hnei : (toReal (P.vert (i + 1))).2 ≠ (toReal (P.vert i)).2)
    (hnej : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2
      ≠ (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (c : ℝ) (hcl : P.edgeThr y i < c) (hcr : c < P.edgeThr y (i + (d : ZMod P.n))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h - y| < δ →
      P.edgeThr h i < c ∧ c < P.edgeThr h (i + (d : ZMod P.n)) := by
  have hconti : Continuous (fun h => P.edgeThr h i) := edgeThr_continuous P i hnei
  have hcontj : Continuous (fun h => P.edgeThr h (i + (d : ZMod P.n))) :=
    edgeThr_continuous P (i + (d : ZMod P.n)) hnej
  -- {h | edgeThr h i < c} is an open nbhd of y
  have hopen_i : IsOpen {h : ℝ | P.edgeThr h i < c} :=
    isOpen_lt hconti continuous_const
  have hopen_j : IsOpen {h : ℝ | c < P.edgeThr h (i + (d : ZMod P.n))} :=
    isOpen_lt continuous_const hcontj
  have hmem_i : y ∈ {h : ℝ | P.edgeThr h i < c} := hcl
  have hmem_j : y ∈ {h : ℝ | c < P.edgeThr h (i + (d : ZMod P.n))} := hcr
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (hopen_i.mem_nhds hmem_i)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp (hopen_j.mem_nhds hmem_j)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun h hh => ?_⟩
  have hh1 : h ∈ Metric.ball y δ₁ := by
    rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hh (min_le_left _ _)
  have hh2 : h ∈ Metric.ball y δ₂ := by
    rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hh (min_le_right _ _)
  exact ⟨hδ₁ hh1, hδ₂ hh2⟩

/-- **The partial-edge crossings straddle a separating column.** For a column `c` strictly
between the two arc-endpoint thresholds, there is `ε > 0` with: (1) the middle run arc stays
above `y+ε`; (2) `y+ε` is below both above-vertices `v_{i+1}`, `v_{i+d}`; (3) `firstPartial`
crosses height `y+ε` at an interior parameter, at column `< c`; (4) `lastPartial` (for the
down-edge `i+d`) crosses height `y+ε` at an interior parameter, at column `> c`. Combines
`run_partials_eps`, `edgeThr_column_nhds`, `firstPartial_hits_eps`/`lastPartial_hits_eps`
and `firstPartial_cross_x`/`lastPartial_cross_x`. This is the geometric column-separation
setup for the ray-sum count in `loopWind_just_above_segment`. -/
lemma partials_straddle_column (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hvert : ∀ k : ℕ, 1 ≤ k → k ≤ d → y < (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (c : ℝ) (hcl : P.edgeThr y i < c) (hcr : c < P.edgeThr y (i + (d : ZMod P.n))) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ s ∈ Set.Icc (0:ℝ) 1, y + ε < (runParam P (i+1) (d-1) s).2) ∧
      (∃ s ∈ Set.Ioo (0:ℝ) 1, (firstPartial P y i s).2 = y + ε ∧
        (firstPartial P y i s).1 < c) ∧
      (∃ s ∈ Set.Ioo (0:ℝ) 1,
        (lastPartial P y (i + (d : ZMod P.n)) s).2 = y + ε ∧
        c < (lastPartial P y (i + (d : ZMod P.n)) s).1) := by
  have hnei : (toReal (P.vert (i + 1))).2 ≠ (toReal (P.vert i)).2 := by
    intro h; linarith [hspi.1, hspi.2]
  have hnej : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2
      ≠ (toReal (P.vert (i + (d : ZMod P.n)))).2 := by
    intro h; linarith [hspj.1, hspj.2]
  obtain ⟨δ, hδpos, hδ⟩ := edgeThr_column_nhds P y i d hnei hnej c hcl hcr
  obtain ⟨ε₀, hε₀pos, hrun, hbelow1, hbelowd⟩ :=
    run_partials_eps P y i d hd hspi hspj hvert
  -- shrink ε₀ so that y+ε is within the column nbhd: |（y+ε)-y| = ε < δ
  set ε := min ε₀ (δ / 2) with hεdef
  have hεpos : 0 < ε := lt_min hε₀pos (by linarith)
  have hle0 : ε ≤ ε₀ := min_le_left _ _
  have hlt_δ : ε < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- column facts at height y+ε
  have hcol : P.edgeThr (y + ε) i < c ∧ c < P.edgeThr (y + ε) (i + (d : ZMod P.n)) := by
    apply hδ
    rw [show y + ε - y = ε by ring, abs_of_pos hεpos]; exact hlt_δ
  -- height bounds
  have hh0 : y < y + ε := by linarith
  have hh1i : y + ε < (toReal (P.vert (i + 1))).2 :=
    lt_of_le_of_lt (show y + ε ≤ y + ε₀ by linarith) hbelow1
  have hh1j : y + ε < (toReal (P.vert (i + (d : ZMod P.n)))).2 :=
    lt_of_le_of_lt (show y + ε ≤ y + ε₀ by linarith) hbelowd
  refine ⟨ε, hεpos, ?_, ?_, ?_⟩
  · intro s hs; have := hrun s hs; linarith
  · -- firstPartial crossing at column < c
    obtain ⟨s, hs, hheight⟩ := firstPartial_hits_eps P y i hspi hh0 hh1i
    refine ⟨s, hs, hheight, ?_⟩
    have hsx := firstPartial_cross_x P y i hspi ⟨le_of_lt hs.1, le_of_lt hs.2⟩ hh0 hh1i hheight
    rw [hsx]; exact hcol.1
  · -- lastPartial crossing at column > c
    obtain ⟨s, hs, hheight⟩ :=
      lastPartial_hits_eps P y (i + (d : ZMod P.n)) hspj hh0 hh1j
    refine ⟨s, hs, hheight, ?_⟩
    have hsx := lastPartial_cross_x P y (i + (d : ZMod P.n)) hspj
      ⟨le_of_lt hs.1, le_of_lt hs.2⟩ hh0 hh1j hheight
    rw [hsx]; exact hcol.2

/-- **The first arc chord crosses height `h` at column `edgeThr h i`.** The first polyline
chord of `arcCorners` is `segment (edgeThr y i, y) v_{i+1}`, a subsegment of `edgeSeg i`
(both endpoints lie on `edgeSeg i`). Hence a point of the chord at height `h`, with
`y < h < v_{i+1}.2`, equals the unique point of `edgeSeg i` at that height,
`(edgeThr h i, h)`, so its x-coordinate is `edgeThr h i`. This identifies the crossing
column of the `arcCorners` polyline's first edge for the ray-sum count. -/
lemma firstChord_cross_x (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (hsp : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    {w : ℝ × ℝ} (hw : w ∈ segment ℝ ((P.edgeThr y i, y) : ℝ × ℝ) (toReal (P.vert (i + 1))))
    {h : ℝ} (hh0 : y < h) (hh1 : h < (toReal (P.vert (i + 1))).2) (hwh : w.2 = h) :
    w.1 = P.edgeThr h i := by
  have hcross : (P.edgeThr y i, y) ∈ P.edgeSeg i := edgeThr_mem_edgeSeg P y i (Or.inl hsp)
  have hend : toReal (P.vert (i + 1)) ∈ P.edgeSeg i := by
    rw [LatticePolygon.edgeSeg]; exact right_mem_segment ℝ _ _
  have hwmem : w ∈ P.edgeSeg i := by
    rw [LatticePolygon.edgeSeg]
    rw [LatticePolygon.edgeSeg] at hcross hend
    exact (convex_segment _ _).segment_subset hcross hend hw
  have hspan_h : (toReal (P.vert i)).2 < h ∧ h < (toReal (P.vert (i + 1))).2 :=
    ⟨lt_trans hsp.1 hh0, hh1⟩
  rw [edgeThr_unique_cross P h i (Or.inl hspan_h) w hwmem hwh]

/-- **The last arc chord crosses height `h` at column `edgeThr h j`.** Companion of
`firstChord_cross_x` for the final polyline chord `segment v_j (edgeThr y j, y)` of
`arcCorners` (the down-edge `j = i+d`): a point of this chord at height `h` with
`y < h < v_j.2` has x-coordinate `edgeThr h j`. -/
lemma lastChord_cross_x (P : LatticePolygon) (y : ℝ) (j : ZMod P.n)
    (hsp : (toReal (P.vert (j + 1))).2 < y ∧ y < (toReal (P.vert j)).2)
    {w : ℝ × ℝ} (hw : w ∈ segment ℝ (toReal (P.vert j)) ((P.edgeThr y j, y) : ℝ × ℝ))
    {h : ℝ} (hh0 : y < h) (hh1 : h < (toReal (P.vert j)).2) (hwh : w.2 = h) :
    w.1 = P.edgeThr h j := by
  have hcross : (P.edgeThr y j, y) ∈ P.edgeSeg j := edgeThr_mem_edgeSeg P y j (Or.inr hsp)
  have hstart : toReal (P.vert j) ∈ P.edgeSeg j := by
    rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _
  have hwmem : w ∈ P.edgeSeg j := by
    rw [LatticePolygon.edgeSeg]
    rw [LatticePolygon.edgeSeg] at hstart hcross
    exact (convex_segment _ _).segment_subset hstart hcross hw
  have hspan_h : (toReal (P.vert (j + 1))).2 < h ∧ h < (toReal (P.vert j)).2 :=
    ⟨lt_trans hsp.1 hh0, hh1⟩
  rw [edgeThr_unique_cross P h j (Or.inr hspan_h) w hwmem hwh]

/-- **The `arcCorners` polyline winds `−1` around a query just above the base height,
between the two threshold columns.** For `q = (c, y+ε)` with the run vertices all strictly
above `y+ε`, a point `w1` of the first chord at height `y+ε` strictly left of `c`, and a
point `w2` of the last chord at height `y+ε` strictly right of `c`:

* the interior run chords have both endpoints above `q` and contribute `0`
  (`chainWind_a_cons_L_append`);
* the first chord spans `q`'s height but its crossing column `w1.1 < c` lies left of the
  rightward ray, so it contributes `0` (`edgeWind_eq_zero_of_up_cross_left`);
* the last chord spans `q`'s height and its crossing column `w2.1 > c` lies right of `q`,
  so the ray meets it and it contributes `−1` (`edgeWind_eq_neg_one_of_down_cross_right`).

Hence `chainWind (arcCorners …) q = −1`. This is the ray-sum count underlying
`loopWind_just_above_segment`. -/
lemma arcCorners_chainWind_count (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hd : 1 ≤ d) (ε c : ℝ) (hε : 0 < ε)
    (w1 : ℝ × ℝ)
    (hw1 : w1 ∈ segment ℝ ((P.edgeThr y i, y) : ℝ × ℝ) (toReal (P.vert (i + 1))))
    (hw1h : w1.2 = y + ε) (hw1c : w1.1 < c)
    (w2 : ℝ × ℝ)
    (hw2 : w2 ∈ segment ℝ (toReal (P.vert (i + (d : ZMod P.n))))
      ((P.edgeThr y (i + (d : ZMod P.n)), y) : ℝ × ℝ))
    (hw2h : w2.2 = y + ε) (hw2c : c < w2.1)
    (hrunabove : ∀ k : ℕ, 1 ≤ k → k ≤ d → y + ε < (toReal (P.vert (i + (k : ZMod P.n)))).2) :
    chainWind (arcCorners P y i d) (c, y + ε) = -1 := by
  set q : ℝ × ℝ := (c, y + ε) with hq
  have hq2 : q.2 = y + ε := rfl
  have hq1 : q.1 = c := rfl
  set f : ℕ → ℝ × ℝ := fun k => toReal (P.vert (i + ((k : ℕ) + 1 : ℕ))) with hf
  have hrun_ne : ((List.range d).map f) ≠ [] := by simp; omega
  have hhead : ((List.range d).map f).head hrun_ne = toReal (P.vert (i + 1)) := by
    rw [List.head_map]; simp [hf]
  have hlast : ((List.range d).map f).getLast hrun_ne
      = toReal (P.vert (i + (d : ZMod P.n))) := by
    rw [List.getLast_map, List.getLast_range]; simp only [hf]; congr 2
    have : ((d - 1 : ℕ) + 1 : ℕ) = d := by omega
    rw [this]
  have harc : arcCorners P y i d
      = (P.edgeThr y i, y) :: ((List.range d).map f)
        ++ [(P.edgeThr y (i + (d : ZMod P.n)), y)] := by
    rw [arcCorners]; rfl
  rw [harc]
  rw [chainWind_a_cons_L_append q _ _ _ hrun_ne (by
    intro p hp
    simp only [hf, List.mem_map, List.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hq2]
    exact hrunabove (k+1) (by omega) (by omega))]
  rw [hhead, hlast]
  have hfirst0 : LatticePolygon.edgeWind (P.edgeThr y i, y) (toReal (P.vert (i + 1))) q = 0 := by
    apply edgeWind_eq_zero_of_up_cross_left _ _ w1 q hw1 (by rw [hw1h, hq2]) _ _
      (by rw [hq1]; exact hw1c)
    · rw [hq2]; simp; linarith
    · rw [hq2]; have := hrunabove 1 (by omega) hd; simpa using this
  have hlast_neg : LatticePolygon.edgeWind (toReal (P.vert (i + (d : ZMod P.n))))
      (P.edgeThr y (i + (d : ZMod P.n)), y) q = -1 := by
    apply edgeWind_eq_neg_one_of_down_cross_right _ _ w2 q hw2 (by rw [hw2h, hq2]) _ _
      (by rw [hq1]; exact hw2c)
    · rw [hq2]; simp; linarith
    · rw [hq2]; exact hrunabove d (by omega) (by omega)
  rw [hfirst0, hlast_neg]; ring

/-- **`loopWind` is nonzero just above the base line, between the two threshold columns.**
For a column `c` strictly between `edgeThr y i` and `edgeThr y (i+d)`, there is a height
margin `ε > 0` with `loopWind P y i d (c, y+ε) ≠ 0`. Indeed `partials_straddle_column`
furnishes such an `ε` together with first and last chord crossing witnesses straddling
`c`, and (since `y+ε > y`) `loopWind` reduces to the open-arc `chainWind`, which the count
`arcCorners_chainWind_count` evaluates to `−1`. The key non-vanishing input that places
`vⱼ₊₁` inside the loop for `vert_succ_j_inside`. -/
lemma loopWind_just_above_segment (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hd : 1 ≤ d)
    (hspi : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)
    (hspj : (toReal (P.vert ((i + (d : ZMod P.n)) + 1))).2 < y ∧
      y < (toReal (P.vert (i + (d : ZMod P.n)))).2)
    (hvert : ∀ k : ℕ, 1 ≤ k → k ≤ d → y < (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (c : ℝ) (hcl : P.edgeThr y i < c) (hcr : c < P.edgeThr y (i + (d : ZMod P.n))) :
    ∃ ε : ℝ, 0 < ε ∧ loopWind P y i d (c, y + ε) ≠ 0 := by
  obtain ⟨ε, hεpos, hrun, ⟨s1, hs1, hs1h, hs1c⟩, ⟨s2, hs2, hs2h, hs2c⟩⟩ :=
    partials_straddle_column P y i d hd hspi hspj hvert c hcl hcr
  refine ⟨ε, hεpos, ?_⟩
  have hrunabove : ∀ k : ℕ, 1 ≤ k → k ≤ d → y + ε < (toReal (P.vert (i + (k : ZMod P.n)))).2 := by
    intro k hk1 hkd
    obtain ⟨s, hs, hseq⟩ := runParam_hits_vertex P (i+1) (d-1) (k-1) (by omega)
    have := hrun s hs
    rw [hseq] at this
    rwa [show (i+1) + ((k-1 : ℕ) : ZMod P.n) = i + (k : ZMod P.n) by
      push_cast; rw [Nat.cast_sub hk1]; push_cast; ring] at this
  have hloop : loopWind P y i d (c, y + ε) = chainWind (arcCorners P y i d) (c, y + ε) :=
    loopWind_eq_chainWind_of_above P y i d _ (by simp; linarith)
  rw [hloop]
  have hw1mem := firstPartial_mem_chord P y i hspi
    (Set.mem_Icc.mpr ⟨le_of_lt hs1.1, le_of_lt hs1.2⟩)
  have hw2mem := lastPartial_mem_chord P y (i + (d : ZMod P.n)) hspj
    (Set.mem_Icc.mpr ⟨le_of_lt hs2.1, le_of_lt hs2.2⟩)
  rw [arcCorners_chainWind_count P y i d hd ε c hεpos
    (firstPartial P y i s1) hw1mem hs1h hs1c
    (lastPartial P y (i + (d : ZMod P.n)) s2) hw2mem hs2h hs2c hrunabove]
  norm_num

/-- **`edgeWind` depends only on `q.2` and the sign of `cross (b-a) (q-a)`.** Two query
points `q, q'` at the *same height* with the *same sign* of `cross (b-a) (·-a)` receive the
same `edgeWind a b`. The `edgeWind` rule is a function of the two height comparisons
`a.2 ≤ q.2`, `q.2 < b.2` (which depend only on `q.2`) and the cross-product sign; equal
height and equal cross-sign fix all three. The seed for horizontal local-constancy of the
winding off the crossing columns. -/
lemma edgeWind_eq_of_height_cross (a b q q' : ℝ × ℝ) (hy : q.2 = q'.2)
    (hcross : (0 < cross (b - a) (q - a) ↔ 0 < cross (b - a) (q' - a)) ∧
      (cross (b - a) (q - a) < 0 ↔ cross (b - a) (q' - a) < 0)) :
    edgeWind a b q = edgeWind a b q' := by
  unfold edgeWind
  rw [hy]
  have hup : (a.2 ≤ q'.2 ∧ q'.2 < b.2 ∧ 0 < cross (b - a) (q - a)) ↔
      (a.2 ≤ q'.2 ∧ q'.2 < b.2 ∧ 0 < cross (b - a) (q' - a)) := by
    rw [and_congr_right_iff]; intro _; rw [and_congr_right_iff]; intro _; exact hcross.1
  have hdn : (b.2 ≤ q'.2 ∧ q'.2 < a.2 ∧ cross (b - a) (q - a) < 0) ↔
      (b.2 ≤ q'.2 ∧ q'.2 < a.2 ∧ cross (b - a) (q' - a) < 0) := by
    rw [and_congr_right_iff]; intro _; rw [and_congr_right_iff]; intro _; exact hcross.2
  simp only [hup, hdn]

/-- **`cross (b-a) (·-a)` is continuous.** As a function of the query point `q`, the
signed area `cross (b-a) (q-a)` is a polynomial (affine) in `q`, hence continuous. Used to
run the intermediate-value argument that forbids a sign change of the cross product along a
segment that avoids the edge's crossing locus. -/
lemma continuous_cross_query (a b : ℝ × ℝ) :
    Continuous (fun q : ℝ × ℝ => cross (b - a) (q - a)) := by
  unfold cross
  fun_prop

/-- **`edgeWind` is constant along a segment avoiding the edge's crossing locus.** If the two
query points `q, q'` share a height (`q.2 = q'.2`) and the cross product `cross (b-a) (·-a)`
never vanishes along the straight segment from `q` to `q'`, then `edgeWind a b q = edgeWind a b q'`.
Indeed the cross product is continuous, so by the intermediate value theorem it keeps a constant
strict sign over the connected segment; equal height plus equal cross-sign forces equal `edgeWind`
via `edgeWind_eq_of_height_cross`. This is per-edge horizontal local-constancy of the winding. -/
lemma edgeWind_eq_of_segment_off_cross (a b q q' : ℝ × ℝ) (hy : q.2 = q'.2)
    (hoff : ∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0) :
    edgeWind a b q = edgeWind a b q' := by
  have hqmem : q ∈ segment ℝ q q' := left_mem_segment ℝ q q'
  have hq'mem : q' ∈ segment ℝ q q' := right_mem_segment ℝ q q'
  have hg0 : cross (b - a) (q - a) ≠ 0 := hoff q hqmem
  have hg1 : cross (b - a) (q' - a) ≠ 0 := hoff q' hq'mem
  have hcont : ContinuousOn (fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a))
      (Set.Icc 0 1) := by
    apply Continuous.continuousOn; simp only [cross]; fun_prop
  have h0 : (fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 0
      = cross (b - a) (q - a) := by norm_num
  have h1 : (fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 1
      = cross (b - a) (q' - a) := by norm_num
  -- no zero of cross strictly between the endpoints (by hoff over the segment)
  have hno : ∀ t ∈ Set.Icc (0:ℝ) 1,
      cross (b - a) (((1 - t) • q + t • q') - a) ≠ 0 := by
    intro t ht
    exact hoff _ ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩
  refine edgeWind_eq_of_height_cross a b q q' hy ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hpos
    rcases lt_trichotomy (cross (b - a) (q' - a)) 0 with hneg | hz | hpos'
    · exfalso
      have hmem : (0:ℝ) ∈ Set.Icc ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 1)
          ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 0) := by
        rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
      obtain ⟨t, ht, htv⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hcont hmem
      exact hno t ht (by simpa using htv)
    · exact absurd hz hg1
    · exact hpos'
  · intro hpos
    rcases lt_trichotomy (cross (b - a) (q - a)) 0 with hneg | hz | hpos'
    · exfalso
      have hmem : (0:ℝ) ∈ Set.Icc ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 0)
          ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 1) := by
        rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
      obtain ⟨t, ht, htv⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont hmem
      exact hno t ht (by simpa using htv)
    · exact absurd hz hg0
    · exact hpos'
  · intro hneg
    rcases lt_trichotomy (cross (b - a) (q' - a)) 0 with hneg' | hz | hpos
    · exact hneg'
    · exact absurd hz hg1
    · exfalso
      have hmem : (0:ℝ) ∈ Set.Icc ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 0)
          ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 1) := by
        rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
      obtain ⟨t, ht, htv⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont hmem
      exact hno t ht (by simpa using htv)
  · intro hneg
    rcases lt_trichotomy (cross (b - a) (q - a)) 0 with hneg' | hz | hpos
    · exact hneg'
    · exact absurd hz hg0
    · exfalso
      have hmem : (0:ℝ) ∈ Set.Icc ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 1)
          ((fun t : ℝ => cross (b - a) (((1 - t) • q + t • q') - a)) 0) := by
        rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
      obtain ⟨t, ht, htv⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hcont hmem
      exact hno t ht (by simpa using htv)

/-- A predicate stating that every consecutive edge `a → b` of the polyline `pts` has its
crossing locus `cross (b-a) (·-a) = 0` avoided along the whole segment from `q` to `q'`. The
hypothesis under which `chainWind pts` is constant across the horizontal segment `q—q'`. -/
def chainOffCross (q q' : ℝ × ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0) ∧ chainOffCross q q' (b :: rest)

lemma chainOffCross_cons₂ (q q' a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    chainOffCross q q' (a :: b :: rest) ↔
      (∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0) ∧ chainOffCross q q' (b :: rest) :=
  Iff.rfl

/-- **Horizontal-segment local constancy of `chainWind`.** If `q` and `q'` share a height and
every consecutive edge of the polyline avoids its crossing locus across the whole segment
`q—q'` (`chainOffCross`), then the open-polyline winding is unchanged from `q` to `q'`. Each
`edgeWind` summand is constant by `edgeWind_eq_of_segment_off_cross`; summing over edges keeps
`chainWind` constant. The polyline analogue of per-edge horizontal local-constancy. -/
lemma chainWind_eq_of_chainOffCross {pts : List (ℝ × ℝ)} {q q' : ℝ × ℝ}
    (hy : q.2 = q'.2) (h : chainOffCross q q' pts) :
    chainWind pts q = chainWind pts q' := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂, chainWind_cons₂]
      rw [chainOffCross_cons₂] at h
      rw [edgeWind_eq_of_segment_off_cross a b q q' hy h.1, ih h.2]

/-- **Horizontal-segment local constancy of `loopWind`.** If `q` and `q'` share a height,
every arc edge avoids its crossing locus across the segment `q—q'` (`chainOffCross` on
`arcCorners`), and the horizontal return edge also avoids its crossing locus there, then
`loopWind P y i d` is unchanged from `q` to `q'`. Combines `chainWind_eq_of_chainOffCross`
for the open arc with `edgeWind_eq_of_segment_off_cross` for the return edge. This is the
local-constancy bridge: along any horizontal motion that meets no edge of the closed curve
`C` (transversally), the winding `loopWind` stays constant. -/
lemma loopWind_eq_of_offCross (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q q' : ℝ × ℝ) (hy : q.2 = q'.2)
    (harc : chainOffCross q q' (arcCorners P y i d))
    (hret : ∀ p ∈ segment ℝ q q',
      cross ((P.edgeThr y i, y) - (P.edgeThr y (i + (d : ZMod P.n)), y))
        (p - (P.edgeThr y (i + (d : ZMod P.n)), y)) ≠ 0) :
    loopWind P y i d q = loopWind P y i d q' := by
  unfold loopWind
  rw [chainWind_eq_of_chainOffCross hy harc,
    edgeWind_eq_of_segment_off_cross _ _ q q' hy hret]

/-- **Sign constancy of a continuous function along a segment.** If `g` is continuous and
nowhere zero on the straight segment `q—q'`, then its strict sign agrees at the two endpoints:
both the positivity and the negativity predicates are preserved. The intermediate value theorem
forbids a sign change over the connected segment. This is the segment-wise sign-locking engine
that drives general (arbitrary-direction) local constancy of the ray-crossing winding. -/
lemma sign_const_of_segment_off {g : ℝ × ℝ → ℝ} (hg : Continuous g) {q q' : ℝ × ℝ}
    (hoff : ∀ p ∈ segment ℝ q q', g p ≠ 0) :
    (0 < g q ↔ 0 < g q') ∧ (g q < 0 ↔ g q' < 0) := by
  have hqmem : q ∈ segment ℝ q q' := left_mem_segment ℝ q q'
  have hq'mem : q' ∈ segment ℝ q q' := right_mem_segment ℝ q q'
  have hg0 : g q ≠ 0 := hoff q hqmem
  have hg1 : g q' ≠ 0 := hoff q' hq'mem
  set f : ℝ → ℝ := fun t : ℝ => g ((1 - t) • q + t • q') with hf
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    apply Continuous.continuousOn; fun_prop
  have h0 : f 0 = g q := by simp [hf]
  have h1 : f 1 = g q' := by simp [hf]
  have hno : ∀ t ∈ Set.Icc (0:ℝ) 1, f t ≠ 0 := by
    intro t ht
    exact hoff _ ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩
  constructor
  · constructor
    · intro hpos
      rcases lt_trichotomy (g q') 0 with hneg | hz | hpos'
      · exfalso
        have hmem : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := by
          rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
        obtain ⟨t, ht, htv⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hcont hmem
        exact hno t ht htv
      · exact absurd hz hg1
      · exact hpos'
    · intro hpos
      rcases lt_trichotomy (g q) 0 with hneg | hz | hpos'
      · exfalso
        have hmem : (0:ℝ) ∈ Set.Icc (f 0) (f 1) := by
          rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
        obtain ⟨t, ht, htv⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont hmem
        exact hno t ht htv
      · exact absurd hz hg0
      · exact hpos'
  · constructor
    · intro hneg
      rcases lt_trichotomy (g q') 0 with hneg' | hz | hpos
      · exact hneg'
      · exact absurd hz hg1
      · exfalso
        have hmem : (0:ℝ) ∈ Set.Icc (f 0) (f 1) := by
          rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
        obtain ⟨t, ht, htv⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont hmem
        exact hno t ht htv
    · intro hneg
      rcases lt_trichotomy (g q) 0 with hneg' | hz | hpos
      · exact hneg'
      · exact absurd hz hg0
      · exfalso
        have hmem : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := by
          rw [h0, h1]; exact ⟨le_of_lt hneg, le_of_lt hpos⟩
        obtain ⟨t, ht, htv⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hcont hmem
        exact hno t ht htv

/-- **`edgeWind` is constant along a segment avoiding all three discontinuity loci.**
If along the whole segment `q—q'` the height never equals `a.2` or `b.2` and the cross product
`cross (b-a) (·-a)` never vanishes, then `edgeWind a b q = edgeWind a b q'`. The three
sign-predicates determining `edgeWind` (`a.2 ≤ ·.2`, `·.2 < b.2`, the cross-sign) are each
locked along the connected segment by `sign_const_of_segment_off`. Unlike
`edgeWind_eq_of_segment_off_cross`, the endpoints need NOT share a height — this is the per-edge
*arbitrary-direction* local constancy of the ray-crossing winding. -/
lemma edgeWind_eq_of_segment_off (a b q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hob : ∀ p ∈ segment ℝ q q', p.2 ≠ b.2)
    (hoc : ∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0) :
    edgeWind a b q = edgeWind a b q' := by
  have hqmem : q ∈ segment ℝ q q' := left_mem_segment ℝ q q'
  have hq'mem : q' ∈ segment ℝ q q' := right_mem_segment ℝ q q'
  -- sign of the three locus functions is locked along the connected segment
  have hsa := sign_const_of_segment_off (g := fun p : ℝ × ℝ => p.2 - a.2)
    (by fun_prop) (q := q) (q' := q') (by intro p hp h; exact hoa p hp (by linarith))
  have hsb := sign_const_of_segment_off (g := fun p : ℝ × ℝ => p.2 - b.2)
    (by fun_prop) (q := q) (q' := q') (by intro p hp h; exact hob p hp (by linarith))
  have hsc := sign_const_of_segment_off (g := fun p : ℝ × ℝ => cross (b - a) (p - a))
    (by simp only [cross]; fun_prop) (q := q) (q' := q') hoc
  -- the four height comparisons agree at q and q' (off the loci, ≤ and < coincide)
  have hle_a : (a.2 ≤ q.2) ↔ (a.2 ≤ q'.2) := by
    have e : ∀ r : ℝ × ℝ, (r.2 ≠ a.2) → (a.2 ≤ r.2 ↔ 0 < r.2 - a.2) := by
      intro r hr; constructor
      · intro h; rcases lt_or_eq_of_le h with h' | h'
        · linarith
        · exact absurd h'.symm hr
      · intro h; linarith
    rw [e q (hoa q hqmem), e q' (hoa q' hq'mem)]; exact hsa.1
  have hlt_a : (q.2 < a.2) ↔ (q'.2 < a.2) := by
    have eq : (q.2 < a.2) ↔ (q.2 - a.2 < 0) := ⟨fun h => by linarith, fun h => by linarith⟩
    have eq' : (q'.2 < a.2) ↔ (q'.2 - a.2 < 0) := ⟨fun h => by linarith, fun h => by linarith⟩
    rw [eq, eq']; exact hsa.2
  have hle_b : (b.2 ≤ q.2) ↔ (b.2 ≤ q'.2) := by
    have e : ∀ r : ℝ × ℝ, (r.2 ≠ b.2) → (b.2 ≤ r.2 ↔ 0 < r.2 - b.2) := by
      intro r hr; constructor
      · intro h; rcases lt_or_eq_of_le h with h' | h'
        · linarith
        · exact absurd h'.symm hr
      · intro h; linarith
    rw [e q (hob q hqmem), e q' (hob q' hq'mem)]; exact hsb.1
  have hlt_b : (q.2 < b.2) ↔ (q'.2 < b.2) := by
    rw [← not_le, ← not_le, hle_b]
  have hP3p : (0 < cross (b - a) (q - a)) ↔ (0 < cross (b - a) (q' - a)) := hsc.1
  have hP3n : (cross (b - a) (q - a) < 0) ↔ (cross (b - a) (q' - a) < 0) := hsc.2
  unfold edgeWind
  exact if_congr (and_congr hle_a (and_congr hlt_b hP3p)) rfl
    (if_congr (and_congr hle_b (and_congr hlt_a hP3n)) rfl rfl)

/-- A predicate stating that every consecutive edge `a → b` of the polyline `pts` avoids, along
the whole segment `q—q'`, all three of its `edgeWind` discontinuity loci: the heights `a.2`,
`b.2`, and the crossing locus `cross (b-a) (·-a) = 0`. The hypothesis under which `chainWind pts`
is constant across the *arbitrary-direction* segment `q—q'` (no shared-height assumption). -/
def chainOffSeg (q q' : ℝ × ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      ((∀ p ∈ segment ℝ q q', p.2 ≠ a.2) ∧ (∀ p ∈ segment ℝ q q', p.2 ≠ b.2) ∧
        (∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0)) ∧ chainOffSeg q q' (b :: rest)

lemma chainOffSeg_cons₂ (q q' a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    chainOffSeg q q' (a :: b :: rest) ↔
      ((∀ p ∈ segment ℝ q q', p.2 ≠ a.2) ∧ (∀ p ∈ segment ℝ q q', p.2 ≠ b.2) ∧
        (∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0)) ∧ chainOffSeg q q' (b :: rest) :=
  Iff.rfl

/-- **Arbitrary-direction local constancy of `chainWind`.** If, along the segment `q—q'`, every
consecutive edge of the polyline avoids all three of its `edgeWind` discontinuity loci
(`chainOffSeg`), then the open-polyline winding is unchanged from `q` to `q'`. Each `edgeWind`
summand is constant by `edgeWind_eq_of_segment_off`; summing over edges keeps `chainWind`
constant. Unlike `chainWind_eq_of_chainOffCross`, the endpoints need NOT share a height. -/
lemma chainWind_eq_of_chainOffSeg {pts : List (ℝ × ℝ)} {q q' : ℝ × ℝ}
    (h : chainOffSeg q q' pts) :
    chainWind pts q = chainWind pts q' := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂, chainWind_cons₂]
      rw [chainOffSeg_cons₂] at h
      rw [edgeWind_eq_of_segment_off a b q q' h.1.1 h.1.2.1 h.1.2.2, ih h.2]

/-- **Arbitrary-direction local constancy of `loopWind` above `y`.** If both endpoints lie
weakly above `y` and the segment `q—q'` avoids all `edgeWind` loci of every arc edge
(`chainOffSeg` on `arcCorners`), then `loopWind P y i d` is unchanged from `q` to `q'`. The
horizontal return edge (height `y`) contributes nothing to either endpoint by
`loopWind_eq_chainWind_of_above`, so only the open arc matters, and that is constant by
`chainWind_eq_of_chainOffSeg`. This is the local-constancy bridge for *non-horizontal* motion
through the region enclosed by `C` (e.g. travelling up an off-`C` spanning edge to a vertex). -/
lemma loopWind_eq_of_offSeg_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q q' : ℝ × ℝ) (hq : y ≤ q.2) (hq' : y ≤ q'.2)
    (harc : chainOffSeg q q' (arcCorners P y i d)) :
    loopWind P y i d q = loopWind P y i d q' := by
  rw [loopWind_eq_chainWind_of_above P y i d q hq,
    loopWind_eq_chainWind_of_above P y i d q' hq']
  exact chainWind_eq_of_chainOffSeg harc

/-- **Two-leg local constancy of `loopWind` above `y`.** Transport along a horizontal leg
`q → m` (constant by `loopWind_eq_of_offCross`, all three legs above `y`) followed by an
arbitrary-direction leg `m → q'` (constant by `loopWind_eq_of_offSeg_above`). All three points
lie weakly above `y`, the horizontal leg shares the height of `q`, and each leg avoids the
relevant discontinuity loci of `C`. Composing the two single-leg bridges gives
`loopWind q = loopWind q'`. This is the path shape used to carry the non-vanishing of `loopWind`
just above the base line out to an above-`y` vertex: a horizontal hop to the spanning column,
then straight up the off-`C` edge. -/
lemma loopWind_eq_of_two_legs_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q m q' : ℝ × ℝ) (hq : y ≤ q.2) (hm : y ≤ m.2) (hq' : y ≤ q'.2)
    (hqm : q.2 = m.2)
    (hcross : chainOffCross q m (arcCorners P y i d))
    (hret : ∀ p ∈ segment ℝ q m,
      cross ((P.edgeThr y i, y) - (P.edgeThr y (i + (d : ZMod P.n)), y))
        (p - (P.edgeThr y (i + (d : ZMod P.n)), y)) ≠ 0)
    (hseg : chainOffSeg m q' (arcCorners P y i d)) :
    loopWind P y i d q = loopWind P y i d q' := by
  rw [loopWind_eq_of_offCross P y i d q m hqm hcross hret]
  exact loopWind_eq_of_offSeg_above P y i d m q' hm hq' hseg

/-- **Height-comparison constancy along a segment avoiding a fixed height `h`.** If every point
of the segment `q—q'` has second coordinate distinct from `h`, then the two strict/weak
comparisons of the endpoint heights against `h` agree. A thin specialization of
`sign_const_of_segment_off` to the affine height function `·.2 − h`, packaged as the four
comparison iffs needed by the shared-vertex cancellation argument. -/
lemma height_cmp_const_of_segment_off {q q' : ℝ × ℝ} (h : ℝ)
    (hoff : ∀ p ∈ segment ℝ q q', p.2 ≠ h) :
    ((h ≤ q.2) ↔ (h ≤ q'.2)) ∧ ((q.2 < h) ↔ (q'.2 < h)) ∧
      ((q.2 ≤ h) ↔ (q'.2 ≤ h)) ∧ ((h < q.2) ↔ (h < q'.2)) := by
  have hqmem : q ∈ segment ℝ q q' := left_mem_segment ℝ q q'
  have hq'mem : q' ∈ segment ℝ q q' := right_mem_segment ℝ q q'
  have hs := sign_const_of_segment_off (g := fun p : ℝ × ℝ => p.2 - h)
    (by fun_prop) (q := q) (q' := q') (by intro p hp hh; exact hoff p hp (by linarith))
  have hq0 : q.2 ≠ h := hoff q hqmem
  have hq'0 : q'.2 ≠ h := hoff q' hq'mem
  -- strict positivity / negativity of `·.2 − h` is locked along the segment
  have hpos : (h < q.2) ↔ (h < q'.2) := by
    have eq : (h < q.2) ↔ (0 < q.2 - h) := ⟨fun hh => by linarith, fun hh => by linarith⟩
    have eq' : (h < q'.2) ↔ (0 < q'.2 - h) := ⟨fun hh => by linarith, fun hh => by linarith⟩
    rw [eq, eq']; exact hs.1
  have hlt : (q.2 < h) ↔ (q'.2 < h) := by
    have eq : (q.2 < h) ↔ (q.2 - h < 0) := ⟨fun hh => by linarith, fun hh => by linarith⟩
    have eq' : (q'.2 < h) ↔ (q'.2 - h < 0) := ⟨fun hh => by linarith, fun hh => by linarith⟩
    rw [eq, eq']; exact hs.2
  -- off the height `h`, weak and strict comparisons coincide
  have hle : (h ≤ q.2) ↔ (h ≤ q'.2) := by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
    constructor
    · rintro (hh | hh)
      · exact Or.inl (hpos.1 hh)
      · exact absurd hh.symm hq0
    · rintro (hh | hh)
      · exact Or.inl (hpos.2 hh)
      · exact absurd hh.symm hq'0
  have hle' : (q.2 ≤ h) ↔ (q'.2 ≤ h) := by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
    constructor
    · rintro (hh | hh)
      · exact Or.inl (hlt.1 hh)
      · exact absurd hh hq0
    · rintro (hh | hh)
      · exact Or.inl (hlt.2 hh)
      · exact absurd hh hq'0
  exact ⟨hle, hlt, hle', hpos⟩

/-- **A segment straddling a height attains it.** If the two endpoints of the segment `q—q'`
lie on opposite (weak) sides of the height `h` (`q.2 ≤ h ≤ q'.2`), then some point of the
segment has second coordinate exactly `h`. Plain IVT on the affine height map; the crossing
witness used to evaluate the cross-product signs at the shared vertex's height. -/
lemma segment_attains_height {q q' : ℝ × ℝ} {h : ℝ}
    (hq : q.2 ≤ h) (hq' : h ≤ q'.2) :
    ∃ p ∈ segment ℝ q q', p.2 = h := by
  set f : ℝ → ℝ := fun t : ℝ => ((1 - t) • q + t • q').2 with hf
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    apply Continuous.continuousOn; fun_prop
  have h0 : f 0 = q.2 := by simp [hf]
  have h1 : f 1 = q'.2 := by simp [hf]
  have hmem : h ∈ Set.Icc (f 0) (f 1) := by rw [h0, h1]; exact ⟨hq, hq'⟩
  obtain ⟨t, ht, htv⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont hmem
  exact ⟨(1 - t) • q + t • q', ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩, htv⟩

/- **Shared-vertex cancellation of the ray-crossing winding.** For a triple of points
`a, b, c` and a query segment `q—q'` that avoids the endpoint heights `a.2`, `c.2`, avoids both
cross-loci `cross (b-a) (·-a) = 0` and `cross (c-b) (·-b) = 0`, and avoids the two actual
segments `[a,b]` and `[b,c]` (but **may** cross the shared height `b.2`), the combined
ray-crossing contribution of the consecutive edges `a→b` and `b→c` is unchanged from `q` to
`q'`:
`edgeWind a b q + edgeWind b c q = edgeWind a b q' + edgeWind b c q'`.
The cross-signs and the comparisons to `a.2`, `c.2` are locked along the connected segment; the
only flippable comparison is to `b.2`, and when the segment straddles `b.2` the jump of
`edgeWind a b` (where `b` is one chord endpoint) is exactly cancelled by the jump of
`edgeWind b c` (where `b` is the other chord's endpoint), as computed from the cross product at
the straddling height. This is the directional core, used in both straddle orientations by
`edgeWind_pair_eq_of_segment_off`. -/
set_option maxHeartbeats 1600000 in
lemma edgeWind_pair_cross (a b c hi lo : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ hi lo, p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ hi lo, p.2 ≠ c.2)
    (hcab : ∀ p ∈ segment ℝ hi lo, cross (b - a) (p - a) ≠ 0)
    (hccb : ∀ p ∈ segment ℝ hi lo, cross (c - b) (p - b) ≠ 0)
    (hsab : ∀ p ∈ segment ℝ hi lo, p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ hi lo, p ∉ segment ℝ b c)
    (hhib : b.2 ≤ hi.2) (hlob : lo.2 < b.2) :
    edgeWind a b hi + edgeWind b c hi = edgeWind a b lo + edgeWind b c lo := by
  have hqmem : hi ∈ segment ℝ hi lo := left_mem_segment ℝ hi lo
  have hq'mem : lo ∈ segment ℝ hi lo := right_mem_segment ℝ hi lo
  obtain ⟨hale, halt, hale', _⟩ := height_cmp_const_of_segment_off a.2 hoa
  obtain ⟨hcle, hclt, hcle', _⟩ := height_cmp_const_of_segment_off c.2 hoc
  have hsab_s := sign_const_of_segment_off (g := fun p : ℝ × ℝ => cross (b - a) (p - a))
    (by simp only [cross]; fun_prop) (q := hi) (q' := lo) hcab
  have hscb_s := sign_const_of_segment_off (g := fun p : ℝ × ℝ => cross (c - b) (p - b))
    (by simp only [cross]; fun_prop) (q := hi) (q' := lo) hccb
  set Cab := cross (b - a) (hi - a) with hCab
  set Cab' := cross (b - a) (lo - a) with hCab'
  set Ccb := cross (c - b) (hi - b) with hCcb
  set Ccb' := cross (c - b) (lo - b) with hCcb'
  have hCab0 : Cab ≠ 0 := hcab hi hqmem
  have hCab'0 : Cab' ≠ 0 := hcab lo hq'mem
  have hCcb0 : Ccb ≠ 0 := hccb hi hqmem
  have hCcb'0 : Ccb' ≠ 0 := hccb lo hq'mem
  have hPab : (0 < Cab) ↔ (0 < Cab') := hsab_s.1
  have hNab : (Cab < 0) ↔ (Cab' < 0) := hsab_s.2
  have hPcb : (0 < Ccb) ↔ (0 < Ccb') := hscb_s.1
  have hNcb : (Ccb < 0) ↔ (Ccb' < 0) := hscb_s.2
  have hcross_ab : ∀ p : ℝ × ℝ, p.2 = b.2 →
      cross (b - a) (p - a) = (b.2 - a.2) * (b.1 - p.1) := by
    intro p hp; simp only [cross, Prod.fst_sub, Prod.snd_sub]; rw [hp]; ring
  have hcross_cb : ∀ p : ℝ × ℝ, p.2 = b.2 →
      cross (c - b) (p - b) = (c.2 - b.2) * (b.1 - p.1) := by
    intro p hp; simp only [cross, Prod.fst_sub, Prod.snd_sub]; rw [hp]; ring
  have getDelta : ∀ p : ℝ × ℝ, p ∈ segment ℝ hi lo → p.2 = b.2 →
      ∃ δ : ℝ, δ ≠ 0 ∧
        ((Cab < 0) ↔ (b.2 - a.2) * δ < 0) ∧ ((0 < Cab) ↔ (0 < (b.2 - a.2) * δ)) ∧
        ((Ccb < 0) ↔ (c.2 - b.2) * δ < 0) ∧ ((0 < Ccb) ↔ (0 < (c.2 - b.2) * δ)) := by
    intro p hp hp2
    refine ⟨b.1 - p.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro hδ
      have hpb : p = b := by
        apply Prod.ext
        · show p.1 = b.1; linarith
        · exact hp2
      exact hsab p hp (by rw [hpb]; exact right_mem_segment ℝ a b)
    all_goals (
      have hsub : segment ℝ hi p ⊆ segment ℝ hi lo :=
        (convex_segment hi lo).segment_subset hqmem hp
      have hsgn := sign_const_of_segment_off
        (g := fun r : ℝ × ℝ => cross (b - a) (r - a)) (by simp only [cross]; fun_prop)
        (q := hi) (q' := p) (fun r hr => hcab r (hsub hr))
      have hsgn' := sign_const_of_segment_off
        (g := fun r : ℝ × ℝ => cross (c - b) (r - b)) (by simp only [cross]; fun_prop)
        (q := hi) (q' := p) (fun r hr => hccb r (hsub hr)))
    · rw [hsgn.2, hcross_ab p hp2]
    · rw [hsgn.1, hcross_ab p hp2]
    · rw [hsgn'.2, hcross_cb p hp2]
    · rw [hsgn'.1, hcross_cb p hp2]
  -- extract a crossing point `p` at height `b.2`
  obtain ⟨p, hpseg', hp2⟩ := segment_attains_height (q := lo) (q' := hi) (h := b.2)
    (le_of_lt hlob) hhib
  rw [segment_symm] at hpseg'
  obtain ⟨δ, hδ, hNabδ, hPabδ, hNcbδ, hPcbδ⟩ := getDelta p hpseg' hp2
  have hAlt : (hi.2 < a.2) ↔ (b.2 - a.2 < 0) := by
    constructor
    · intro h; linarith
    · intro h; by_contra hcon; push_neg at hcon
      exact absurd (hale.mp hcon) (by linarith)
  have hClt : (hi.2 < c.2) ↔ (0 < c.2 - b.2) := by
    constructor
    · intro h; linarith
    · intro h; by_contra hcon; push_neg at hcon
      exact absurd (hcle.mp hcon) (by linarith)
  have e1 : edgeWind a b hi = (if hi.2 < a.2 ∧ Cab < 0 then (-1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCab]
    rw [if_neg (show ¬ (a.2 ≤ hi.2 ∧ hi.2 < b.2 ∧ 0 < Cab) by rintro ⟨_, h, _⟩; linarith)]
    exact if_congr ⟨fun ⟨_, h₂, h₃⟩ => ⟨h₂, h₃⟩, fun ⟨h₂, h₃⟩ => ⟨hhib, h₂, h₃⟩⟩ rfl rfl
  have e2 : edgeWind b c hi = (if hi.2 < c.2 ∧ 0 < Ccb then (1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCcb]
    rw [if_congr (show (b.2 ≤ hi.2 ∧ hi.2 < c.2 ∧ 0 < Ccb) ↔ (hi.2 < c.2 ∧ 0 < Ccb) from
      ⟨fun ⟨_, h₂, h₃⟩ => ⟨h₂, h₃⟩, fun ⟨h₂, h₃⟩ => ⟨hhib, h₂, h₃⟩⟩) rfl rfl]
    rw [if_neg (show ¬ (c.2 ≤ hi.2 ∧ hi.2 < b.2 ∧ Ccb < 0) by rintro ⟨_, h, _⟩; linarith)]
  have e3 : edgeWind a b lo = (if a.2 ≤ lo.2 ∧ 0 < Cab' then (1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCab']
    rw [if_congr (show (a.2 ≤ lo.2 ∧ lo.2 < b.2 ∧ 0 < Cab') ↔ (a.2 ≤ lo.2 ∧ 0 < Cab') from
      ⟨fun ⟨h₁, _, h₃⟩ => ⟨h₁, h₃⟩, fun ⟨h₁, h₃⟩ => ⟨h₁, hlob, h₃⟩⟩) rfl rfl]
    rw [if_neg (show ¬ (b.2 ≤ lo.2 ∧ lo.2 < a.2 ∧ Cab' < 0) by rintro ⟨h, _, _⟩; linarith)]
  have e4 : edgeWind b c lo = (if c.2 ≤ lo.2 ∧ Ccb' < 0 then (-1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCcb']
    rw [if_neg (show ¬ (b.2 ≤ lo.2 ∧ lo.2 < c.2 ∧ 0 < Ccb') by rintro ⟨h, _, _⟩; linarith)]
    exact if_congr ⟨fun ⟨h₁, _, h₃⟩ => ⟨h₁, h₃⟩, fun ⟨h₁, h₃⟩ => ⟨h₁, hlob, h₃⟩⟩ rfl rfl
  rw [e1, e2, e3, e4]
  have hprod_ab : (b.2 - a.2) * δ ≠ 0 := by
    rcases (lt_or_gt_of_ne hCab0) with h | h
    · exact ne_of_lt (hNabδ.mp h)
    · exact ne_of_gt (hPabδ.mp h)
  have hprod_cb : (c.2 - b.2) * δ ≠ 0 := by
    rcases (lt_or_gt_of_ne hCcb0) with h | h
    · exact ne_of_lt (hNcbδ.mp h)
    · exact ne_of_gt (hPcbδ.mp h)
  have hba : b.2 - a.2 ≠ 0 := fun h => hprod_ab (by rw [h, zero_mul])
  have hcb : c.2 - b.2 ≠ 0 := fun h => hprod_cb (by rw [h, zero_mul])
  have hq'a : (a.2 ≤ lo.2) ↔ (0 < b.2 - a.2) := by
    rw [← hale]; constructor
    · intro h; rcases lt_or_gt_of_ne hba with hh | hh
      · exact absurd (hAlt.mpr hh) (by linarith)
      · linarith
    · intro h; by_contra hcon; push_neg at hcon
      exact absurd (hAlt.mp hcon) (by linarith)
  have hq'c : (c.2 ≤ lo.2) ↔ (c.2 - b.2 < 0) := by
    rw [← hcle]; constructor
    · intro h; rcases lt_or_gt_of_ne hcb with hh | hh
      · linarith
      · exact absurd (hClt.mpr hh) (by linarith)
    · intro h; by_contra hcon; push_neg at hcon
      exact absurd (hClt.mp hcon) (by linarith)
  have hPab' : (0 < Cab') ↔ (0 < (b.2 - a.2) * δ) := hPab.symm.trans hPabδ
  have hNcb' : (Ccb' < 0) ↔ ((c.2 - b.2) * δ < 0) := hNcb.symm.trans hNcbδ
  simp only [ite_and, hAlt, hNabδ, hClt, hPcbδ, hq'a, hPab', hq'c, hNcb']
  rcases lt_or_gt_of_ne hba with hsab' | hsab' <;>
    rcases lt_or_gt_of_ne hcb with hscb' | hscb' <;>
    rcases lt_or_gt_of_ne hδ with hsδ | hsδ <;>
    split_ifs <;>
      first
        | decide
        | (exfalso; nlinarith [hsab', hscb', hsδ, mul_self_nonneg δ])

set_option maxHeartbeats 1600000 in
lemma edgeWind_pair_eq_of_segment_off (a b c q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hcab : ∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0)
    (hccb : ∀ p ∈ segment ℝ q q', cross (c - b) (p - b) ≠ 0)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b c) :
    edgeWind a b q + edgeWind b c q = edgeWind a b q' + edgeWind b c q' := by
  have hqmem : q ∈ segment ℝ q q' := left_mem_segment ℝ q q'
  have hq'mem : q' ∈ segment ℝ q q' := right_mem_segment ℝ q q'
  -- comparisons to a.2 and c.2 are constant along the segment
  obtain ⟨hale, halt, hale', _⟩ := height_cmp_const_of_segment_off a.2 hoa
  obtain ⟨hcle, hclt, hcle', _⟩ := height_cmp_const_of_segment_off c.2 hoc
  -- cross-signs constant along the segment
  have hsab_s := sign_const_of_segment_off (g := fun p : ℝ × ℝ => cross (b - a) (p - a))
    (by simp only [cross]; fun_prop) (q := q) (q' := q') hcab
  have hscb_s := sign_const_of_segment_off (g := fun p : ℝ × ℝ => cross (c - b) (p - b))
    (by simp only [cross]; fun_prop) (q := q) (q' := q') hccb
  -- abbreviations for the (constant-sign) cross products at the two endpoints
  set Cab := cross (b - a) (q - a) with hCab
  set Cab' := cross (b - a) (q' - a) with hCab'
  set Ccb := cross (c - b) (q - b) with hCcb
  set Ccb' := cross (c - b) (q' - b) with hCcb'
  have hCab0 : Cab ≠ 0 := hcab q hqmem
  have hCab'0 : Cab' ≠ 0 := hcab q' hq'mem
  have hCcb0 : Ccb ≠ 0 := hccb q hqmem
  have hCcb'0 : Ccb' ≠ 0 := hccb q' hq'mem
  -- the two cross-sign iffs as separate positivity / negativity equivalences
  have hPab : (0 < Cab) ↔ (0 < Cab') := hsab_s.1
  have hNab : (Cab < 0) ↔ (Cab' < 0) := hsab_s.2
  have hPcb : (0 < Ccb) ↔ (0 < Ccb') := hscb_s.1
  have hNcb : (Ccb < 0) ↔ (Ccb' < 0) := hscb_s.2
  -- In a non-crossing branch, the comparison to `b.2` is also constant (`hb`), so each
  -- `edgeWind` is individually constant by congruence of the two `if`-conditions.
  have nonCross : ∀ (hb : (q.2 < b.2) ↔ (q'.2 < b.2)) (hble : (b.2 ≤ q.2) ↔ (b.2 ≤ q'.2)),
      edgeWind a b q + edgeWind b c q = edgeWind a b q' + edgeWind b c q' := by
    intro hb hble
    have eab : edgeWind a b q = edgeWind a b q' := by
      unfold edgeWind
      rw [← hCab, ← hCab']
      exact if_congr (and_congr hale (and_congr hb hsab_s.1)) rfl
        (if_congr (and_congr hble (and_congr halt hsab_s.2)) rfl rfl)
    have ebc : edgeWind b c q = edgeWind b c q' := by
      unfold edgeWind
      rw [← hCcb, ← hCcb']
      exact if_congr (and_congr hble (and_congr hclt hscb_s.1)) rfl
        (if_congr (and_congr hcle (and_congr hb hscb_s.2)) rfl rfl)
    rw [eab, ebc]
  -- Main split on the side of `b.2`.
  rcases le_or_gt b.2 q.2 with hqb | hqb <;> rcases le_or_gt b.2 q'.2 with hq'b | hq'b
  · -- both ≥ b.2 : non-crossing
    refine nonCross ?_ ?_
    · constructor <;> intro h <;> [exact absurd hqb (not_le.mpr h); exact absurd hq'b (not_le.mpr h)]
    · exact ⟨fun _ => hq'b, fun _ => hqb⟩
  · -- q ≥ b.2, q' < b.2 : crossing (q above, q' below)
    exact edgeWind_pair_cross a b c q q' hoa hoc hcab hccb hsab hscb hqb hq'b
  · -- q < b.2, q' ≥ b.2 : crossing (q below, q' above)
    refine (edgeWind_pair_cross a b c q' q ?_ ?_ ?_ ?_ ?_ ?_ hq'b hqb).symm
    · intro p hp; exact hoa p (by rwa [segment_symm] at hp)
    · intro p hp; exact hoc p (by rwa [segment_symm] at hp)
    · intro p hp; exact hcab p (by rwa [segment_symm] at hp)
    · intro p hp; exact hccb p (by rwa [segment_symm] at hp)
    · intro p hp; exact hsab p (by rwa [segment_symm] at hp)
    · intro p hp; exact hscb p (by rwa [segment_symm] at hp)
  · -- both < b.2 : non-crossing
    refine nonCross ?_ ?_
    · exact ⟨fun _ => hq'b, fun _ => hqb⟩
    · constructor <;> intro h <;> [exact absurd h (not_le.mpr hqb); exact absurd h (not_le.mpr hq'b)]

/-- **`edgeWind` is antisymmetric off the two endpoint heights.** If the query height
`q.2` differs from both `a.2` and `b.2`, then reversing the edge negates its winding
contribution: `edgeWind b a q = - edgeWind a b q`. (At an exact endpoint height the
half-open `≤ / <` convention breaks this, hence the two off-height hypotheses.) The key
fact `cross (a-b) (q-b) = - cross (b-a) (q-a)` flips the cross-sign in lockstep with the
swapped height comparisons. -/
lemma edgeWind_neg_of_off (a b q : ℝ × ℝ) (ha : q.2 ≠ a.2) (hb : q.2 ≠ b.2) :
    LatticePolygon.edgeWind b a q = - LatticePolygon.edgeWind a b q := by
  have hc : cross (a - b) (q - b) = - cross (b - a) (q - a) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  unfold LatticePolygon.edgeWind
  rw [hc]
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb' <;>
    rcases lt_trichotomy (cross (b - a) (q - a)) 0 with hcr | hcr | hcr <;>
    split_ifs <;>
    (try (exfalso; revert ha hb;
          (try obtain ⟨s1, s2, s3⟩ := «_ ∧ _ ∧ _»); intros; linarith)) <;>
    simp_all <;> linarith

/-- **A horizontal edge contributes nothing.** If the directed edge `a → b` is horizontal
(`a.2 = b.2`), the ray-crossing rule gives `edgeWind a b q = 0`: both conditional branches
demand a strict height comparison `q.2 < b.2` resp. `q.2 < a.2` together with the opposite
weak one, which `a.2 = b.2` makes impossible. (A horizontal segment is never crossed
transversally by the horizontal ray, so it never changes the winding.) -/
lemma edgeWind_eq_zero_of_eq_height (a b q : ℝ × ℝ) (h : a.2 = b.2) :
    LatticePolygon.edgeWind a b q = 0 := by
  unfold LatticePolygon.edgeWind
  split_ifs with h1 h2
  · obtain ⟨u, v, _⟩ := h1; rw [h] at u; linarith
  · obtain ⟨u, v, _⟩ := h2; rw [h] at v; linarith
  · rfl

/-- **Twice-signed-area identity for the triangle loop.** Writing `P = cross (a-x) (q-x)`,
`Q = cross (b-a) (q-a)`, `R = cross (x-b) (q-b)` for the three (consistently loop-oriented)
cross products of the closed triangle path `x → a → b → x` around `q`, their sum is the
query-independent twice-signed-area `cross (a-x) (b-x)` of the triangle. This is the algebraic
core of triangle winding additivity: the dependence on `q` cancels in the loop sum. -/
lemma cross_triangle_loop_sum (x a b q : ℝ × ℝ) :
    cross (a - x) (q - x) + cross (b - a) (q - a) + cross (x - b) (q - b)
      = cross (a - x) (b - x) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- **Telescoping identity for the broken path vs. direct edge.** The closed triangle cross
product `cross (b-x) (q-x)` of the direct edge `x → b` decomposes as the sum of the two
sub-edge cross products `cross (a-x) (q-x)` and `cross (b-a) (q-a)` plus the constant
twice-signed-area term `cross (b-a) (a-x)`. (Companion of `cross_triangle_loop_sum`, used to
relate the broken path `x → a → b` to the direct edge `x → b`.) -/
lemma cross_path_split (x a b q : ℝ × ℝ) :
    cross (b - x) (q - x)
      = cross (a - x) (q - x) + cross (b - a) (q - a) + cross (b - a) (a - x) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- **Vertex-elimination via segment transport for the triangle loop.** The closed-loop
`edgeWind` sum of the broken path `x → a → b → x` is constant along any segment `q—q'` that
stays off all of the three edges' `edgeWind` discontinuity loci (endpoint heights and crossing
loci). This is the segment-transport form underlying STEP B's vertex elimination: each of the
three `edgeWind` summands is individually constant by `edgeWind_eq_of_segment_off`, packaged
through `chainWind`/`chainOffSeg` for the polyline `[x, a, b, x]`. -/
lemma edgeWind_three_eq_of_segment_off (x a b q q' : ℝ × ℝ)
    (hxa : (∀ p ∈ segment ℝ q q', p.2 ≠ x.2) ∧ (∀ p ∈ segment ℝ q q', p.2 ≠ a.2) ∧
      (∀ p ∈ segment ℝ q q', cross (a - x) (p - x) ≠ 0))
    (hab : (∀ p ∈ segment ℝ q q', p.2 ≠ a.2) ∧ (∀ p ∈ segment ℝ q q', p.2 ≠ b.2) ∧
      (∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0))
    (hbx : (∀ p ∈ segment ℝ q q', p.2 ≠ b.2) ∧ (∀ p ∈ segment ℝ q q', p.2 ≠ x.2) ∧
      (∀ p ∈ segment ℝ q q', cross (x - b) (p - b) ≠ 0)) :
    LatticePolygon.edgeWind x a q + LatticePolygon.edgeWind a b q + LatticePolygon.edgeWind b x q
      = LatticePolygon.edgeWind x a q' + LatticePolygon.edgeWind a b q' +
        LatticePolygon.edgeWind b x q' := by
  have hc : chainWind [x, a, b, x] q = chainWind [x, a, b, x] q' := by
    apply chainWind_eq_of_chainOffSeg
    rw [chainOffSeg_cons₂, chainOffSeg_cons₂, chainOffSeg_cons₂]
    exact ⟨hxa, hab, hbx, trivial⟩
  rw [chainWind_cons₂, chainWind_cons₂, chainWind_cons₂, chainWind_singleton] at hc
  rw [chainWind_cons₂, chainWind_cons₂, chainWind_cons₂, chainWind_singleton] at hc
  linarith [hc]

/-- **Line ∩ open height-band ⟹ on the chord segment (either endpoint order).** A point `w`
on the line through `a, b` (`cross (b-a) (w-a) = 0`) whose height lies weakly between the two
endpoint heights lies on the segment `[a, b]`, regardless of which of `a.2`, `b.2` is larger.
This is the symmetric companion of `mem_segment_of_cross_zero`, packaging the "a point of the
chord's line with height in the chord's band is on the chord segment" fact for use with the
arbitrary orientation of an arc edge. -/
lemma mem_segment_of_cross_zero' (a b w : ℝ × ℝ) (hab : a.2 ≠ b.2)
    (hcross : cross (b - a) (w - a) = 0)
    (hlo : min a.2 b.2 ≤ w.2) (hhi : w.2 ≤ max a.2 b.2) :
    w ∈ segment ℝ a b := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a.2 < b.2
    rw [min_eq_left hlt.le] at hlo
    rw [max_eq_right hlt.le] at hhi
    exact mem_segment_of_cross_zero a b w hlt hcross hlo hhi
  · -- b.2 < a.2, so use the reversed segment
    rw [min_eq_right hgt.le] at hlo
    rw [max_eq_left hgt.le] at hhi
    rw [segment_symm]
    have hc : cross (a - b) (w - b) = 0 := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub] at hcross ⊢; linarith
    exact mem_segment_of_cross_zero b a w hgt hc hlo hhi

/-- **Inside the strict height-band of a chord, being off the chord segment forces off its
line.** If the query segment `q—q'` is disjoint from the chord `[a, b]` (`a.2 ≠ b.2`), then any
point `p` of the query segment whose height lies *strictly* inside the chord's height band
`(min a.2 b.2, max a.2 b.2)` has `cross (b-a) (p-a) ≠ 0`: were it zero, `p` would be on the
chord's line and, with height in the open band, on the chord segment — contradicting
disjointness. This is the technical core of the prompt's KEY INSIGHT ("within the band the
chord's line coincides with the chord segment"): the off-cross-locus hypothesis needed by the
segment-transport lemmas is *automatic* from mere segment disjointness, but only inside the open
band. -/
lemma cross_ne_zero_of_band_of_seg_disjoint (a b q q' : ℝ × ℝ) (hab : a.2 ≠ b.2)
    (hdisj : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (p : ℝ × ℝ) (hp : p ∈ segment ℝ q q')
    (hlo : min a.2 b.2 < p.2) (hhi : p.2 < max a.2 b.2) :
    cross (b - a) (p - a) ≠ 0 := by
  intro h0
  exact hdisj p hp (mem_segment_of_cross_zero' a b p hab h0 (le_of_lt hlo) (le_of_lt hhi))

/-- **Per-edge local constancy of `edgeWind` for an up-going chord, from mere segment
disjointness.** For a chord `a → b` with `a.2 < b.2`, if the query segment `q—q'` avoids both
endpoint heights `a.2`, `b.2` *and* is disjoint from the chord segment `[a, b]`, then
`edgeWind a b q = edgeWind a b q'`. Avoiding the two endpoint heights confines the whole query
segment to a single open height-region (it cannot cross the boundary heights `a.2` or `b.2`):
below `a.2` and above `b.2` both `edgeWind`s vanish (`edgeWind_eq_zero_of_below`/`_above`); in
the strict interior band `(a.2, b.2)` segment disjointness upgrades to off-the-cross-line
(`cross_ne_zero_of_band_of_seg_disjoint`), so the off-locus transport
`edgeWind_eq_of_segment_off` applies. This realizes the prompt's KEY INSIGHT at the single-edge
level: within the band the chord's line coincides with the chord segment, so being off the
*segment* already locks the cross-sign — no off-*line* hypothesis is needed there. -/
lemma edgeWind_eq_of_seg_disjoint_of_lt (a b q q' : ℝ × ℝ) (hab : a.2 < b.2)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hob : ∀ p ∈ segment ℝ q q', p.2 ≠ b.2)
    (hdisj : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b) :
    edgeWind a b q = edgeWind a b q' := by
  have hqmem : q ∈ segment ℝ q q' := left_mem_segment ℝ q q'
  have hq'mem : q' ∈ segment ℝ q q' := right_mem_segment ℝ q q'
  obtain ⟨_, halt, _, _⟩ := height_cmp_const_of_segment_off a.2 hoa
  obtain ⟨hble, hblt, _, hbpos⟩ := height_cmp_const_of_segment_off b.2 hob
  rcases lt_trichotomy q.2 a.2 with hqa | hqa | hqa
  · have hq'a : q'.2 < a.2 := halt.mp hqa
    rw [edgeWind_eq_zero_of_below a b q hqa (by linarith),
        edgeWind_eq_zero_of_below a b q' hq'a (by linarith)]
  · exact absurd hqa (hoa q hqmem)
  · rcases lt_trichotomy q.2 b.2 with hqb | hqb | hqb
    · refine edgeWind_eq_of_segment_off a b q q' hoa hob (fun p hp => ?_)
      have hsub : segment ℝ q p ⊆ segment ℝ q q' :=
        (convex_segment q q').segment_subset (left_mem_segment ℝ q q') hp
      obtain ⟨_, _, _, hpos⟩ := height_cmp_const_of_segment_off a.2 (fun r hr => hoa r (hsub hr))
      obtain ⟨_, hplt, _, _⟩ := height_cmp_const_of_segment_off b.2 (fun r hr => hob r (hsub hr))
      exact cross_ne_zero_of_band_of_seg_disjoint a b q q' (ne_of_lt hab) hdisj p hp
        (by rw [min_eq_left hab.le]; exact hpos.mp hqa)
        (by rw [max_eq_right hab.le]; exact hplt.mp hqb)
    · exact absurd hqb (hob q hqmem)
    · have hq'b : b.2 < q'.2 := hbpos.mp hqb
      rw [edgeWind_eq_zero_of_above a b q (by linarith) (by linarith),
          edgeWind_eq_zero_of_above a b q' (by linarith) (by linarith)]

/-- **Per-edge local constancy of `edgeWind` from mere segment disjointness (any orientation).**
For an arbitrary chord `a → b`, if the query segment `q—q'` avoids both endpoint heights and is
disjoint from the chord segment `[a, b]`, then `edgeWind a b q = edgeWind a b q'`. The three
orientations are handled uniformly: a horizontal chord (`a.2 = b.2`) gives `edgeWind = 0` at both
ends (`edgeWind_eq_zero_of_eq_height`); an up-going chord is `edgeWind_eq_of_seg_disjoint_of_lt`;
a down-going chord reduces to the up-going case on the reversed chord `b → a` (same segment, same
disjointness) via the unconditional antisymmetry `edgeWind a b · = − edgeWind b a ·`
(`edgeWind_antisymm`). This is the single-edge realization of the prompt's KEY INSIGHT: a query
segment disjoint from the chord segment (and off its endpoint heights) cannot change that edge's
ray-crossing contribution. -/
lemma edgeWind_eq_of_seg_disjoint (a b q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hob : ∀ p ∈ segment ℝ q q', p.2 ≠ b.2)
    (hdisj : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b) :
    edgeWind a b q = edgeWind a b q' := by
  rcases lt_trichotomy a.2 b.2 with hlt | heq | hgt
  · exact edgeWind_eq_of_seg_disjoint_of_lt a b q q' hlt hoa hob hdisj
  · rw [edgeWind_eq_zero_of_eq_height a b q heq, edgeWind_eq_zero_of_eq_height a b q' heq]
  · -- down-going: work on the reversed chord b → a (same segment, same disjointness)
    have hdisj' : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b a := by
      intro p hp; rw [segment_symm]; exact hdisj p hp
    have hrev : edgeWind b a q = edgeWind b a q' :=
      edgeWind_eq_of_seg_disjoint_of_lt b a q q' hgt hob hoa hdisj'
    have e1 := edgeWind_antisymm a b q
    have e2 := edgeWind_antisymm a b q'
    omega

/-- A predicate stating that every consecutive edge `a → b` of the polyline `pts` has, along the
whole query segment `q—q'`, its two endpoint heights `a.2`, `b.2` avoided *and* its chord segment
`[a, b]` disjoint from the query segment. The hypothesis under which `chainWind pts` is constant
across `q—q'` using only *segment* disjointness (no off-cross-line assumption), via
`edgeWind_eq_of_seg_disjoint`. -/
def chainSegDisjoint (q q' : ℝ × ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      ((∀ p ∈ segment ℝ q q', p.2 ≠ a.2) ∧ (∀ p ∈ segment ℝ q q', p.2 ≠ b.2) ∧
        (∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)) ∧ chainSegDisjoint q q' (b :: rest)

lemma chainSegDisjoint_cons₂ (q q' a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    chainSegDisjoint q q' (a :: b :: rest) ↔
      ((∀ p ∈ segment ℝ q q', p.2 ≠ a.2) ∧ (∀ p ∈ segment ℝ q q', p.2 ≠ b.2) ∧
        (∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)) ∧ chainSegDisjoint q q' (b :: rest) :=
  Iff.rfl

/-- **List-level local constancy of `chainWind` from segment disjointness.** If, along the query
segment `q—q'`, every consecutive edge of the polyline avoids its two endpoint heights and has its
chord segment disjoint from `q—q'` (`chainSegDisjoint`), then the open-polyline winding is
unchanged from `q` to `q'`. Each `edgeWind` summand is constant by `edgeWind_eq_of_seg_disjoint`;
summing over edges keeps `chainWind` constant. This is the polyline lift of the prompt's KEY
INSIGHT: only being off the chord *segments* (plus the endpoint heights) is required — no
off-cross-line hypothesis. -/
lemma chainWind_eq_of_seg_disjoint {pts : List (ℝ × ℝ)} {q q' : ℝ × ℝ}
    (h : chainSegDisjoint q q' pts) :
    chainWind pts q = chainWind pts q' := by
  induction pts with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      rw [chainWind_cons₂, chainWind_cons₂]
      rw [chainSegDisjoint_cons₂] at h
      rw [edgeWind_eq_of_seg_disjoint a b q q' h.1.1 h.1.2.1 h.1.2.2, ih h.2]

/-- **Local constancy of `loopWind` above `y` from segment disjointness.** If both endpoints lie
weakly above `y` and the query segment `q—q'` avoids the endpoint heights of, and is disjoint from
the chord segments of, every arc edge (`chainSegDisjoint` on `arcCorners`), then `loopWind P y i d`
is unchanged from `q` to `q'`. The horizontal return edge (height `y`) contributes nothing to
either endpoint by `loopWind_eq_chainWind_of_above`, so only the open arc matters, and that is
constant by `chainWind_eq_of_seg_disjoint`. This is the loop-level transport along a segment that
merely avoids the *arc edge-segments* — the shape used to carry the just-above-base non-vanishing
of `loopWind` up an off-`C` edge to a vertex. -/
lemma loopWind_eq_of_seg_disjoint_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q q' : ℝ × ℝ) (hq : y ≤ q.2) (hq' : y ≤ q'.2)
    (harc : chainSegDisjoint q q' (arcCorners P y i d)) :
    loopWind P y i d q = loopWind P y i d q' := by
  rw [loopWind_eq_chainWind_of_above P y i d q hq,
    loopWind_eq_chainWind_of_above P y i d q' hq']
  exact chainWind_eq_of_seg_disjoint harc

/-- **A chord point at an endpoint's height is that endpoint.** If `p0 ∈ [a, b]` has height
`p0.2 = b.2` and the chord is non-horizontal (`a.2 ≠ b.2`), then `p0 = b`. The convex-combination
weight on `a` must vanish (its height contribution would otherwise pull `p0.2` away from `b.2`),
forcing `p0 = b`. The geometric fact behind "the only point of a non-horizontal chord at the top
(or bottom) endpoint's height is that endpoint". -/
lemma mem_segment_height_eq_endpoint (a b p0 : ℝ × ℝ) (hab : a.2 ≠ b.2) (hp0 : p0.2 = b.2)
    (hmem : p0 ∈ segment ℝ a b) : p0 = b := by
  obtain ⟨s, t, hs, ht, hst, hpt⟩ := hmem
  have hy : p0.2 = s * a.2 + t * b.2 := by rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
  have heq : s * a.2 + t * b.2 = b.2 := by rw [← hy, hp0]
  have ht' : t = 1 - s := by linarith
  subst ht'
  have hd : s * (a.2 - b.2) = 0 := by nlinarith [heq]
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hd with h | h
    · exact h
    · exact absurd (by linarith : a.2 = b.2) hab
  rw [← hpt, hs0]; simp

/-- **Off the chord, a point at the shared height has nonzero cross.** If `p0` has height `b.2`
and is *not* equal to `b`, then `cross (b-a) (p0-a) ≠ 0` for any `a` with `a.2 ≠ b.2`. Were the
cross zero, `p0` would lie on the chord's line and (its height `b.2` being a chord endpoint
height) on the chord segment, hence equal to `b` by `mem_segment_height_eq_endpoint` — a
contradiction. The key continuity seed for the crossing branch of the pair lemma: at the exact
shared height, the two consecutive chords meet only at `b`, so the cross products of both chords
are nonzero at any other point of that height. -/
lemma cross_ne_zero_of_height_ne (a b p0 : ℝ × ℝ) (hab : a.2 ≠ b.2) (hp0 : p0.2 = b.2)
    (hne : p0 ≠ b) : cross (b - a) (p0 - a) ≠ 0 := by
  intro h0
  apply hne
  refine mem_segment_height_eq_endpoint a b p0 hab hp0 ?_
  refine mem_segment_of_cross_zero' a b p0 hab h0 ?_ ?_
  · rw [hp0]; exact min_le_right _ _
  · rw [hp0]; exact le_max_right _ _

/-- **Pair constancy of `edgeWind` from segment disjointness, when the shared height `b.2` is
avoided.** If the query segment `q—q'` avoids the heights `a.2`, `b.2`, `c.2` and is disjoint
from both chord segments `[a,b]`, `[b,c]`, then the combined ray-crossing contribution of the
consecutive edges `a→b` and `b→c` is unchanged. Each `edgeWind` summand is *individually*
constant by `edgeWind_eq_of_seg_disjoint` (no off-cross-line hypothesis is needed, only segment
disjointness plus the two endpoint heights). This is the non-crossing branch of the general pair
lemma; the genuine cancellation only occurs when the segment straddles `b.2`. -/
lemma edgeWind_pair_eq_of_seg_disjoint_off_mid (a b c q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hob : ∀ p ∈ segment ℝ q q', p.2 ≠ b.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b c) :
    edgeWind a b q + edgeWind b c q = edgeWind a b q' + edgeWind b c q' := by
  rw [edgeWind_eq_of_seg_disjoint a b q q' hoa hob hsab,
      edgeWind_eq_of_seg_disjoint b c q q' hob hoc hscb]

/-- **Pair constancy across a single shared-height crossing (non-horizontal edges).** When the
query segment `q—q'` straddles the shared height `b.2` strictly (`q'.2 < b.2 < q.2`), avoids the
outer heights `a.2`, `c.2`, is disjoint from both chord segments `[a,b]`, `[b,c]`, and both edges
are non-horizontal (`a.2 ≠ b.2`, `c.2 ≠ b.2`), the combined ray-crossing contribution is
unchanged. The segment meets the height `b.2` at a unique point `p0`, which is off `b` (hence off
both chord lines, so both cross products are nonzero there). By continuity there is a small
straddling sub-segment `[u, v] ⊆ [q, q']` (with `v.2 < b.2 < u.2`) on which both cross products
stay nonzero; `edgeWind_pair_eq_of_segment_off` gives constancy of the pair sum across the
crossing on `[u, v]`. The two outer pieces `[q, u]` and `[v, q']` each avoid `b.2` (it is hit only
inside `[u, v]`), so the pair sum is individually constant there by
`edgeWind_pair_eq_of_seg_disjoint_off_mid`. Chaining the three equalities closes the crossing
case. -/
lemma edgeWind_pair_eq_cross_seg_disjoint (a b c q q' : ℝ × ℝ)
    (hab : a.2 ≠ b.2) (hcb : c.2 ≠ b.2)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b c)
    (hqhi : b.2 < q.2) (hqlo : q'.2 < b.2) :
    edgeWind a b q + edgeWind b c q = edgeWind a b q' + edgeWind b c q' := by
  -- parametrize the query segment
  set γ : ℝ → ℝ × ℝ := fun τ => (1 - τ) • q + τ • q' with hγ
  have hγcont : Continuous γ := by fun_prop
  have hγ0 : γ 0 = q := by simp [hγ]
  have hγ1 : γ 1 = q' := by simp [hγ]
  have hγmem : ∀ τ ∈ Set.Icc (0:ℝ) 1, γ τ ∈ segment ℝ q q' := by
    intro τ hτ; exact ⟨1 - τ, τ, by linarith [hτ.2], hτ.1, by ring, rfl⟩
  -- height along the segment is affine: γ τ).2 = (1-τ)*q.2 + τ*q'.2
  have hH : ∀ τ : ℝ, (γ τ).2 = (1 - τ) * q.2 + τ * q'.2 := by
    intro τ; simp [hγ, Prod.snd_add, Prod.smul_snd]
  -- the crossing parameter
  set τ0 : ℝ := (q.2 - b.2) / (q.2 - q'.2) with hτ0def
  have hden : 0 < q.2 - q'.2 := by linarith
  have hτ0mem : τ0 ∈ Set.Ioo (0:ℝ) 1 := by
    constructor
    · apply div_pos (by linarith) hden
    · rw [div_lt_one hden]; linarith
  have hHτ0 : (γ τ0).2 = b.2 := by
    rw [hH τ0, hτ0def]; field_simp; ring
  set p0 : ℝ × ℝ := γ τ0 with hp0def
  have hp0mem : p0 ∈ segment ℝ q q' := hγmem τ0 ⟨le_of_lt hτ0mem.1, le_of_lt hτ0mem.2⟩
  have hp0ne : p0 ≠ b := by
    intro h; exact hsab p0 hp0mem (by rw [h]; exact right_mem_segment ℝ a b)
  -- both cross products are nonzero at p0
  have hFab0 : cross (b - a) (p0 - a) ≠ 0 := cross_ne_zero_of_height_ne a b p0 hab hHτ0 hp0ne
  have hFcb0 : cross (c - b) (p0 - b) ≠ 0 := by
    have : cross (b - c) (p0 - c) ≠ 0 := cross_ne_zero_of_height_ne c b p0 hcb hHτ0 hp0ne
    intro h; apply this
    have : cross (b - c) (p0 - c) = - cross (c - b) (p0 - b) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [this, h, neg_zero]
  -- continuity: cross products as functions of τ
  set Fab : ℝ → ℝ := fun τ => cross (b - a) (γ τ - a) with hFabdef
  set Fcb : ℝ → ℝ := fun τ => cross (c - b) (γ τ - b) with hFcbdef
  have hFabcont : Continuous Fab := by simp only [hFabdef, cross]; fun_prop
  have hFcbcont : Continuous Fcb := by simp only [hFcbdef, cross]; fun_prop
  have hFabτ0 : Fab τ0 ≠ 0 := hFab0
  have hFcbτ0 : Fcb τ0 ≠ 0 := hFcb0
  -- eventually nonzero near τ0
  have hev : ∀ᶠ τ in nhds τ0, Fab τ ≠ 0 ∧ Fcb τ ≠ 0 :=
    ((hFabcont.continuousAt).eventually_ne hFabτ0).and ((hFcbcont.continuousAt).eventually_ne hFcbτ0)
  obtain ⟨δ, hδpos, hball⟩ := Metric.eventually_nhds_iff.mp hev
  -- choose a small straddling radius
  set r : ℝ := min (δ / 2) (min (τ0 / 2) ((1 - τ0) / 2)) with hrdef
  have hrpos : 0 < r := by
    apply lt_min (by linarith)
    exact lt_min (by linarith [hτ0mem.1]) (by linarith [hτ0mem.2])
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrlo : 0 < τ0 - r := by
    have : r ≤ τ0 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hτ0mem.1]
  have hrhi : τ0 + r < 1 := by
    have : r ≤ (1 - τ0) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [hτ0mem.2]
  set τu : ℝ := τ0 - r with hτudef
  set τv : ℝ := τ0 + r with hτvdef
  set u : ℝ × ℝ := γ τu with hudef
  set v : ℝ × ℝ := γ τv with hvdef
  have hτumem : τu ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hτvmem : τv ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have humem : u ∈ segment ℝ q q' := hγmem τu hτumem
  have hvmem : v ∈ segment ℝ q q' := hγmem τv hτvmem
  -- the sub-segment [u, v] lies in [q, q']
  have hsub : segment ℝ u v ⊆ segment ℝ q q' :=
    (convex_segment q q').segment_subset humem hvmem
  -- cross nonzero on [τu, τv] (within the ball)
  have hballall : ∀ τ ∈ Set.Icc τu τv, Fab τ ≠ 0 ∧ Fcb τ ≠ 0 := by
    intro τ hτ
    apply hball
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- γ is affine: a convex combination of γ α and γ β is γ of the combination
  have hγaff : ∀ (α β s : ℝ), (1 - s) • γ α + s • γ β = γ ((1 - s) * α + s * β) := by
    intro α β s
    simp only [hγ]
    have hx : ((1 - ((1 - s) * α + s * β)) : ℝ) = (1 - s) * (1 - α) + s * (1 - β) := by ring
    rw [hx]
    module
  -- any point of [γ α, γ β] (α ≤ β) is γ of a parameter in [α, β]
  have hmemparam2 : ∀ (α β : ℝ), α ≤ β → ∀ p ∈ segment ℝ (γ α) (γ β),
      ∃ τ ∈ Set.Icc α β, p = γ τ := by
    intro α β hαβ p hp
    obtain ⟨s, t, hs, ht, hst, hpt⟩ := hp
    have hs' : s = 1 - t := by linarith
    refine ⟨(1 - t) * α + t * β, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [hαβ]
    · nlinarith [hαβ]
    · rw [← hpt, hs', ← hγaff α β t]
  -- any point of [u, v] is γ of a parameter in [τu, τv]
  have hmemparam : ∀ p ∈ segment ℝ u v, ∃ τ ∈ Set.Icc τu τv, p = γ τ := by
    intro p hp
    exact hmemparam2 τu τv (by linarith) p (by rw [hudef, hvdef] at hp; exact hp)
  -- cross products nonzero on the sub-segment [u, v]
  have hcab_uv : ∀ p ∈ segment ℝ u v, cross (b - a) (p - a) ≠ 0 := by
    intro p hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam p hp
    rw [hpτ]; exact (hballall τ hτ).1
  have hccb_uv : ∀ p ∈ segment ℝ u v, cross (c - b) (p - b) ≠ 0 := by
    intro p hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam p hp
    rw [hpτ]; exact (hballall τ hτ).2
  -- pair sum is constant across the crossing on [u, v]
  have hmid : edgeWind a b u + edgeWind b c u = edgeWind a b v + edgeWind b c v :=
    edgeWind_pair_eq_of_segment_off a b c u v
      (fun p hp => hoa p (hsub hp)) (fun p hp => hoc p (hsub hp))
      hcab_uv hccb_uv
      (fun p hp => hsab p (hsub hp)) (fun p hp => hscb p (hsub hp))
  -- the outer pieces [q, u] and [v, q'] avoid the shared height b.2
  -- height is strictly decreasing in τ, equal to b.2 only at τ0
  have hHmono : ∀ τ1 τ2 : ℝ, τ1 < τ2 → (γ τ2).2 < (γ τ1).2 := by
    intro τ1 τ2 h12
    rw [hH τ1, hH τ2]; nlinarith [hden, h12]
  have hob_qu : ∀ p ∈ segment ℝ q u, p.2 ≠ b.2 := by
    intro p hp
    -- [q, u] = γ([0, τu]); on it height ≥ (γ τu).2 > b.2
    rw [← hγ0] at hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam2 0 τu (by linarith) p hp
    rw [hpτ]
    have : b.2 < (γ τu).2 := by
      have := hHmono τu τ0 (by linarith); rw [hHτ0] at this; exact this
    have hmono2 : (γ τu).2 ≤ (γ τ).2 := by
      rcases eq_or_lt_of_le hτ.2 with h | h
      · rw [h]
      · exact le_of_lt (hHmono τ τu h)
    linarith
  have hob_vq : ∀ p ∈ segment ℝ v q', p.2 ≠ b.2 := by
    intro p hp
    rw [← hγ1] at hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam2 τv 1 (by linarith) p hp
    rw [hpτ]
    have hlt : (γ τv).2 < b.2 := by
      have := hHmono τ0 τv (by linarith); rw [hHτ0] at this; exact this
    have hmono2 : (γ τ).2 ≤ (γ τv).2 := by
      rcases eq_or_lt_of_le hτ.1 with h | h
      · rw [← h]
      · exact le_of_lt (hHmono τv τ h)
    linarith
  -- subsegment helpers: [q, u] avoids a.2, c.2, [a,b], [b,c] (sub of [q, q'])
  have hsubqu : segment ℝ q u ⊆ segment ℝ q q' :=
    (convex_segment q q').segment_subset (left_mem_segment ℝ q q') humem
  have hsubvq : segment ℝ v q' ⊆ segment ℝ q q' :=
    (convex_segment q q').segment_subset hvmem (right_mem_segment ℝ q q')
  have hleft : edgeWind a b q + edgeWind b c q = edgeWind a b u + edgeWind b c u :=
    edgeWind_pair_eq_of_seg_disjoint_off_mid a b c q u
      (fun p hp => hoa p (hsubqu hp)) hob_qu (fun p hp => hoc p (hsubqu hp))
      (fun p hp => hsab p (hsubqu hp)) (fun p hp => hscb p (hsubqu hp))
  have hright : edgeWind a b v + edgeWind b c v = edgeWind a b q' + edgeWind b c q' :=
    edgeWind_pair_eq_of_seg_disjoint_off_mid a b c v q'
      (fun p hp => hoa p (hsubvq hp)) hob_vq (fun p hp => hoc p (hsubvq hp))
      (fun p hp => hsab p (hsubvq hp)) (fun p hp => hscb p (hsubvq hp))
  rw [hleft, hmid, hright]

/-- **Pair constancy of `edgeWind` from segment disjointness (the general step-1 lemma).** If the
query segment `q—q'` avoids the outer heights `a.2`, `c.2`, has both endpoints off the shared
height `b.2` (`q.2 ≠ b.2`, `q'.2 ≠ b.2`), and is disjoint from both chord segments `[a,b]`,
`[b,c]`, then the combined ray-crossing contribution of the consecutive edges `a→b` and `b→c` is
unchanged — even though the segment may freely **cross** `b.2` in its interior. This is the
prompt's KEY upgrade of `edgeWind_pair_eq_of_segment_off`: the off-cross-line hypotheses are
discharged purely from segment disjointness. A horizontal edge (`a.2 = b.2` or `c.2 = b.2`)
contributes `0` and the sum reduces to the other edge's individual constancy. Otherwise, if both
endpoints lie on the same side of `b.2` the whole (height-affine) segment avoids `b.2` and each
edge is individually constant (`edgeWind_pair_eq_of_seg_disjoint_off_mid`); if the endpoints
straddle `b.2` the shared-vertex cancellation across the unique crossing
(`edgeWind_pair_eq_cross_seg_disjoint`) keeps the sum fixed. This pairwise cancellation is exactly
what lets `chainWind` transport across a segment that crosses interior vertex heights. -/
lemma edgeWind_pair_eq_of_seg_disjoint (a b c q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hqb : q.2 ≠ b.2) (hq'b : q'.2 ≠ b.2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b c) :
    edgeWind a b q + edgeWind b c q = edgeWind a b q' + edgeWind b c q' := by
  -- horizontal-edge reductions: a horizontal edge contributes 0, leaving one edge
  by_cases hab : a.2 = b.2
  · rw [edgeWind_eq_zero_of_eq_height a b q hab, edgeWind_eq_zero_of_eq_height a b q' hab]
    rw [edgeWind_eq_of_seg_disjoint b c q q' (fun p hp => by rw [← hab]; exact hoa p hp) hoc hscb]
  by_cases hcb : c.2 = b.2
  · rw [edgeWind_eq_zero_of_eq_height b c q hcb.symm, edgeWind_eq_zero_of_eq_height b c q' hcb.symm]
    rw [edgeWind_eq_of_seg_disjoint a b q q' hoa (fun p hp => hcb ▸ hoc p hp) hsab]
  -- both edges non-horizontal: split on the side of `b.2`
  rcases lt_or_gt_of_ne hqb with hqlt | hqgt <;> rcases lt_or_gt_of_ne hq'b with hq'lt | hq'gt
  · -- both below b.2: whole segment avoids b.2 (height affine, endpoints below)
    refine edgeWind_pair_eq_of_seg_disjoint_off_mid a b c q q' hoa ?_ hoc hsab hscb
    intro p hp
    obtain ⟨s, t, hs, ht, hst, hpt⟩ := hp
    have hh : p.2 = s * q.2 + t * q'.2 := by rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
    intro hpb
    rw [hpb] at hh
    have hsum : s * b.2 + t * b.2 = b.2 := by rw [← add_mul, hst, one_mul]
    have h1 : s * q.2 ≤ s * b.2 := mul_le_mul_of_nonneg_left hqlt.le hs
    have h2 : t * q'.2 ≤ t * b.2 := mul_le_mul_of_nonneg_left hq'lt.le ht
    rcases lt_or_eq_of_le hs with hsp | hs0
    · have h3 : s * q.2 < s * b.2 := mul_lt_mul_of_pos_left hqlt hsp
      linarith [h1, h2, h3, hsum, hh]
    · have ht1 : t = 1 := by linarith
      have h3 : t * q'.2 < t * b.2 := by rw [ht1]; simpa using hq'lt
      linarith [h1, h2, h3, hsum, hh]
  · -- q below, q' above: straddle (reverse orientation)
    exact (edgeWind_pair_eq_cross_seg_disjoint a b c q' q hab hcb
      (fun p hp => hoa p (by rwa [segment_symm] at hp))
      (fun p hp => hoc p (by rwa [segment_symm] at hp))
      (fun p hp => hsab p (by rwa [segment_symm] at hp))
      (fun p hp => hscb p (by rwa [segment_symm] at hp)) hq'gt hqlt).symm
  · -- q above, q' below: straddle (direct orientation)
    exact edgeWind_pair_eq_cross_seg_disjoint a b c q q' hab hcb hoa hoc hsab hscb hqgt hq'lt
  · -- both above b.2: whole segment avoids b.2
    refine edgeWind_pair_eq_of_seg_disjoint_off_mid a b c q q' hoa ?_ hoc hsab hscb
    intro p hp
    obtain ⟨s, t, hs, ht, hst, hpt⟩ := hp
    have hh : p.2 = s * q.2 + t * q'.2 := by rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
    intro hpb
    rw [hpb] at hh
    have hsum : s * b.2 + t * b.2 = b.2 := by rw [← add_mul, hst, one_mul]
    have h1 : s * b.2 ≤ s * q.2 := mul_le_mul_of_nonneg_left hqgt.le hs
    have h2 : t * b.2 ≤ t * q'.2 := mul_le_mul_of_nonneg_left hq'gt.le ht
    rcases lt_or_eq_of_le hs with hsp | hs0
    · have h3 : s * b.2 < s * q.2 := mul_lt_mul_of_pos_left hqgt hsp
      linarith [h1, h2, h3, hsum, hh]
    · have ht1 : t = 1 := by linarith
      have h3 : t * b.2 < t * q'.2 := by rw [ht1]; simpa using hq'gt
      linarith [h1, h2, h3, hsum, hh]

/-- **Strong segment-disjoint transport of `chainWind` across a single interior vertex.** For the
three-corner polyline `[a, b, c]` (one interior vertex `b`), the open-polyline winding is unchanged
along a query segment `q—q'` that is disjoint from both chord segments `[a, b]`, `[b, c]` and avoids
only the **outer** heights `a.2`, `c.2` (with both endpoints off the middle height `b.2`). The
interior height `b.2` is *allowed to be crossed*: the crossing is absorbed by the strengthened
per-vertex cancellation `edgeWind_pair_eq_of_seg_disjoint`. This is the `d = 1` (single interior
vertex) instance of the strong chain-transport that step 1 of the `vert_succ_j_inside` plan needs;
the general (many interior vertices) version requires height-monotone slicing not done here. -/
lemma chainWind_eq_of_seg_disjoint_strong3 (a b c q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hqb : q.2 ≠ b.2) (hq'b : q'.2 ≠ b.2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b c) :
    chainWind [a, b, c] q = chainWind [a, b, c] q' := by
  rw [chainWind_cons₂, chainWind_cons₂, chainWind_singleton,
      chainWind_cons₂, chainWind_cons₂, chainWind_singleton]
  have hpair := edgeWind_pair_eq_of_seg_disjoint a b c q q' hoa hoc hqb hq'b hsab hscb
  simp only [add_zero]
  linarith [hpair]

/-- **Strong segment-disjoint transport of `loopWind` above `y` for a single-step arc (`d = 1`).**
For the crossing arc `i → i+1` whose only interior corner is the vertex `v_{i+1}`, `loopWind P y i 1`
is unchanged along a query segment `q—q'` lying weakly above `y` that is disjoint from the two arc
chord segments `[(edgeThr y i, y), v_{i+1}]` and `[v_{i+1}, (edgeThr y (i+1), y)]` and avoids only the
two threshold heights (both equal to `y`), while being permitted to *cross* the interior vertex height
`(v_{i+1}).2`. The horizontal return edge (height `y`) contributes nothing at either endpoint
(`loopWind_eq_chainWind_of_above`), so only the open arc matters, and that is constant by
`chainWind_eq_of_seg_disjoint_strong3`. This is the loop-level form of step 1 (single interior vertex)
in the `vert_succ_j_inside` plan: transport that may cross the interior vertex height, needed because a
leg climbing toward `v_{i+1}` straddles that height. -/
lemma loopWind_eq_of_seg_disjoint_strong3_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n)
    (q q' : ℝ × ℝ) (hq : y ≤ q.2) (hq' : y ≤ q'.2)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ (P.edgeThr y i, y).2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ (P.edgeThr y (i + (1 : ZMod P.n)), y).2)
    (hqb : q.2 ≠ (toReal (P.vert (i + 1))).2) (hq'b : q'.2 ≠ (toReal (P.vert (i + 1))).2)
    (hsab : ∀ p ∈ segment ℝ q q',
      p ∉ segment ℝ (P.edgeThr y i, y) (toReal (P.vert (i + 1))))
    (hscb : ∀ p ∈ segment ℝ q q',
      p ∉ segment ℝ (toReal (P.vert (i + 1))) (P.edgeThr y (i + (1 : ZMod P.n)), y)) :
    loopWind P y i 1 q = loopWind P y i 1 q' := by
  rw [loopWind_eq_chainWind_of_above P y i 1 q hq,
      loopWind_eq_chainWind_of_above P y i 1 q' hq']
  have harc : arcCorners P y i 1
      = [(P.edgeThr y i, y), toReal (P.vert (i + 1)), (P.edgeThr y (i + (1 : ZMod P.n)), y)] := by
    unfold arcCorners; simp [List.range_succ]
  rw [harc]
  exact chainWind_eq_of_seg_disjoint_strong3 _ _ _ q q' hoa hoc hqb hq'b hsab hscb

/-- **Splitting a height-monotone segment at an interior height.** If `q.2 < q'.2` and
`q.2 < h < q'.2`, the unique point `m ∈ [q,q']` at height `h` splits the segment: `[q,m]` and
`[m,q']` are both subsegments of `[q,q']`, the height along `[q,m]` is `≤ h` and along `[m,q']`
is `≥ h`. -/
lemma segment_split_at_height {q q' : ℝ × ℝ} {h : ℝ}
    (hqq' : q.2 < q'.2) (hh0 : q.2 < h) (hh1 : h < q'.2) :
    ∃ m ∈ segment ℝ q q', m.2 = h ∧
      segment ℝ q m ⊆ segment ℝ q q' ∧ segment ℝ m q' ⊆ segment ℝ q q' ∧
      (∀ p ∈ segment ℝ q m, p.2 ≤ h) ∧ (∀ p ∈ segment ℝ m q', h ≤ p.2) := by
  set t : ℝ := (h - q.2) / (q'.2 - q.2) with htdef
  have hden : 0 < q'.2 - q.2 := by linarith
  have ht0 : 0 < t := div_pos (by linarith) hden
  have ht1 : t < 1 := by rw [htdef, div_lt_one hden]; linarith
  set m : ℝ × ℝ := (1 - t) • q + t • q' with hmdef
  have hmmem : m ∈ segment ℝ q q' := ⟨1 - t, t, by linarith, by linarith, by ring, rfl⟩
  have hm2 : m.2 = h := by
    rw [hmdef]; simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [htdef]; field_simp; ring
  refine ⟨m, hmmem, hm2, ?_, ?_, ?_, ?_⟩
  · exact (convex_segment q q').segment_subset (left_mem_segment ℝ q q') hmmem
  · exact (convex_segment q q').segment_subset hmmem (right_mem_segment ℝ q q')
  · -- height on [q, m] is ≤ h: q.2 < h and m.2 = h, height affine between
    intro p hp
    obtain ⟨s₁, s₂, hs₁, hs₂, hsum, hpt⟩ := hp
    have hh : p.2 = s₁ * q.2 + s₂ * m.2 := by
      rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
    rw [hh, hm2]
    have : s₁ * q.2 ≤ s₁ * h := mul_le_mul_of_nonneg_left (le_of_lt hh0) hs₁
    rw [show s₂ = 1 - s₁ from by linarith]; nlinarith [this]
  · intro p hp
    obtain ⟨s₁, s₂, hs₁, hs₂, hsum, hpt⟩ := hp
    have hh : p.2 = s₁ * m.2 + s₂ * q'.2 := by
      rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
    rw [hh, hm2]
    have : s₂ * h ≤ s₂ * q'.2 := mul_le_mul_of_nonneg_left (le_of_lt hh1) hs₂
    rw [show s₁ = 1 - s₂ from by linarith]; nlinarith [this]

/-- **`chainWind` transport crossing only the first interior vertex height.** For a polyline
`a :: b :: c :: rest`, if the query segment is disjoint from every chord, avoids the height of `a`
and the height of *every* vertex of `c :: rest`, but is allowed to **cross** the height `b.2` of
the single interior vertex `b`, then the open-polyline winding is unchanged. The first two edges
`a→b`, `b→c` are transported together by `edgeWind_pair_eq_of_seg_disjoint` (the `b.2` crossing is
absorbed by the shared-vertex cancellation), while the remaining suffix `c :: rest` avoids all its
heights and is transported edge-by-edge by `chainWind_eq_of_seg_disjoint`. -/
lemma chainWind_eq_of_seg_disjoint_cross_head2 (a b c : ℝ × ℝ) (rest : List (ℝ × ℝ))
    (q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hqb : q.2 ≠ b.2) (hq'b : q'.2 ≠ b.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b c)
    (hrest : chainSegDisjoint q q' (c :: rest)) :
    chainWind (a :: b :: c :: rest) q = chainWind (a :: b :: c :: rest) q' := by
  have hpair := edgeWind_pair_eq_of_seg_disjoint a b c q q' hoa hoc hqb hq'b hsab hscb
  have hsuf := chainWind_eq_of_seg_disjoint (pts := c :: rest) (q := q) (q' := q') hrest
  rw [chainWind_cons₂, chainWind_cons₂, chainWind_cons₂, chainWind_cons₂]
  linarith [hpair, hsuf]

/-- **`chainWind` transport crossing only one designated interior vertex height (arbitrary
position).** The query segment is allowed to **cross** the single height `b.2` of the interior
vertex `b` (flanked by `a` then `c`), while along the whole prefix `front ++ [a]` it avoids all
vertex heights and chord segments (`chainSegDisjoint`), and along the suffix `c :: rest` likewise.
By induction on `front`: each prefix edge is individually constant
(`edgeWind_eq_of_seg_disjoint`), and the base case is
`chainWind_eq_of_seg_disjoint_cross_head2`. This lets a height-monotone query segment carry
`chainWind` across exactly one interior vertex height located anywhere in the polyline. -/
lemma chainWind_eq_of_seg_disjoint_cross_one (front : List (ℝ × ℝ)) (a b c : ℝ × ℝ)
    (rest : List (ℝ × ℝ)) (q q' : ℝ × ℝ)
    (hfront : chainSegDisjoint q q' (front ++ [a]))
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hqb : q.2 ≠ b.2) (hq'b : q'.2 ≠ b.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b c)
    (hrest : chainSegDisjoint q q' (c :: rest)) :
    chainWind (front ++ a :: b :: c :: rest) q = chainWind (front ++ a :: b :: c :: rest) q' := by
  induction front with
  | nil =>
    simpa using chainWind_eq_of_seg_disjoint_cross_head2 a b c rest q q'
      hoa hqb hq'b hoc hsab hscb hrest
  | cons x front' ih =>
    -- head of the appended tail (it is nonempty)
    set M : List (ℝ × ℝ) := front' ++ a :: b :: c :: rest with hM
    have hMne : M ≠ [] := by rw [hM]; exact List.append_ne_nil_of_right_ne_nil _ (by simp)
    obtain ⟨z, zs, hMzs⟩ := List.exists_cons_of_ne_nil hMne
    -- the head `z` of M equals the head of `front' ++ [a]`
    have hfront_cons : chainSegDisjoint q q' (x :: (front' ++ [a])) := by
      simpa using hfront
    cases front' with
    | nil =>
      -- M = a :: b :: c :: rest, z = a, edge x→a is the only prefix edge
      have hMa : M = a :: b :: c :: rest := by rw [hM]; simp
      rw [List.nil_append] at *
      show chainWind (x :: a :: b :: c :: rest) q = chainWind (x :: a :: b :: c :: rest) q'
      rw [chainWind_cons₂ x a, chainWind_cons₂ x a]
      have hxa := ((chainSegDisjoint_cons₂ q q' x a []).mp (by simpa using hfront_cons :
        chainSegDisjoint q q' (x :: a :: []))).1
      rw [edgeWind_eq_of_seg_disjoint x a q q' hxa.1 hxa.2.1 hxa.2.2]
      have := chainWind_eq_of_seg_disjoint_cross_head2 a b c rest q q'
        hoa hqb hq'b hoc hsab hscb hrest
      linarith [this]
    | cons w front'' =>
      have hMw : M = w :: (front'' ++ a :: b :: c :: rest) := by rw [hM]; simp
      show chainWind (x :: M) q = chainWind (x :: M) q'
      rw [hMw, chainWind_cons₂, chainWind_cons₂]
      have hfrontw : chainSegDisjoint q q' (x :: w :: (front'' ++ [a])) := by
        simpa using hfront_cons
      have hxw := ((chainSegDisjoint_cons₂ q q' x w (front'' ++ [a])).mp hfrontw).1
      have htail : chainSegDisjoint q q' (w :: (front'' ++ [a])) :=
        ((chainSegDisjoint_cons₂ q q' x w (front'' ++ [a])).mp hfrontw).2
      rw [edgeWind_eq_of_seg_disjoint x w q q' hxw.1 hxw.2.1 hxw.2.2]
      have hih := ih (by simpa using htail)
      rw [hMw] at hih
      linarith [hih]

/-- **Structural decomposition of `arcCorners` at an interior vertex.** For `1 ≤ k ≤ d`, the
crossing-arc corner list `arcCorners P y i d` can be written as `front ++ a :: b :: c :: rest`
where `b = v_{i+k}` is the `k`-th interior vertex, `a` is the corner just before it (the threshold
corner `(edgeThr y i, y)` when `k = 1`, otherwise `v_{i+k-1}`), and `c` is the corner just after
it (the closing threshold corner `(edgeThr y (i+d), y)` when `k = d`, otherwise `v_{i+k+1}`). This
exhibits any interior vertex in the `front ++ a::b::c::rest` shape required by
`chainWind_eq_of_seg_disjoint_cross_one`. -/
lemma arcCorners_split_at_vertex (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (k : ℕ) (hk1 : 1 ≤ k) (hkd : k ≤ d) :
    ∃ (front rest : List (ℝ × ℝ)) (a c : ℝ × ℝ),
      arcCorners P y i d
        = front ++ a :: toReal (P.vert (i + (k : ZMod P.n))) :: c :: rest := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hlen : (arcCorners P y i d).length = d + 2 := by
    unfold arcCorners; simp [List.length_append]
  -- index m+1 of arcCorners holds the interior vertex v_{i+(m+1)}
  have hget : (arcCorners P y i d)[m + 1]'(by omega)
      = toReal (P.vert (i + ((m + 1 : ℕ) : ZMod P.n))) := by
    unfold arcCorners
    rw [List.getElem_cons_succ]
    rw [List.getElem_append_left (by simp; omega)]
    rw [List.getElem_map, List.getElem_range]
  set L := arcCorners P y i d with hL
  -- the three exposed indices m, m+1, m+2 are all in range
  have hmL : m < L.length := by omega
  have hm1L : m + 1 < L.length := by omega
  have hm2L : m + 2 < L.length := by omega
  -- split L at index m, exposing L[m], L[m+1] (= vertex), L[m+2]
  refine ⟨L.take m, L.drop (m + 3), L[m]'hmL, L[m+2]'hm2L, ?_⟩
  conv_lhs => rw [← List.take_append_drop m L]
  rw [List.drop_eq_getElem_cons hmL, List.drop_eq_getElem_cons hm1L,
      List.drop_eq_getElem_cons hm2L]
  rw [show L[m+1]'hm1L = toReal (P.vert (i + ((m + 1 : ℕ) : ZMod P.n))) from hget]

/-- **`chainWind` transport across exactly one interior arc vertex.** For the crossing-arc corner
list `arcCorners P y i d` and an interior vertex `v_{i+k}` (`1 ≤ k ≤ d`), the open-polyline winding
is unchanged along a query segment `q—q'` that is allowed to **cross** the height `(v_{i+k}).2` of
that single vertex, provided: the prefix `front ++ [a]` up to the corner `a` just before the vertex
and the suffix `c :: rest` from the corner `c` just after it are both `chainSegDisjoint` from `q—q'`
(avoiding all their corner heights and chords), the segment avoids the heights of the flanking
corners `a`, `c`, has both endpoints off the vertex height, and is disjoint from the two chords
`[a, v_{i+k}]`, `[v_{i+k}, c]`. Obtained by exhibiting the vertex in `front ++ a::b::c::rest` form
via `arcCorners_split_at_vertex` and applying `chainWind_eq_of_seg_disjoint_cross_one`. This is the
single-vertex step of the height-monotone `chainWind` transport that step 1 of the
`vert_succ_j_inside` plan iterates. -/
lemma chainWind_arc_cross_one_vertex (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (k : ℕ) (hk1 : 1 ≤ k) (hkd : k ≤ d) (q q' : ℝ × ℝ)
    {front rest : List (ℝ × ℝ)} {a c : ℝ × ℝ}
    (hsplit : arcCorners P y i d
      = front ++ a :: toReal (P.vert (i + (k : ZMod P.n))) :: c :: rest)
    (hfront : chainSegDisjoint q q' (front ++ [a]))
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hqb : q.2 ≠ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (hq'b : q'.2 ≠ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hsab : ∀ p ∈ segment ℝ q q',
      p ∉ segment ℝ a (toReal (P.vert (i + (k : ZMod P.n)))))
    (hscb : ∀ p ∈ segment ℝ q q',
      p ∉ segment ℝ (toReal (P.vert (i + (k : ZMod P.n)))) c)
    (hrest : chainSegDisjoint q q' (c :: rest)) :
    chainWind (arcCorners P y i d) q = chainWind (arcCorners P y i d) q' := by
  rw [hsplit]
  exact chainWind_eq_of_seg_disjoint_cross_one front a
    (toReal (P.vert (i + (k : ZMod P.n)))) c rest q q'
    hfront hoa hqb hq'b hoc hsab hscb hrest

/-- **`chainSegDisjoint` is inherited by the tail.** Dropping the head of a polyline preserves
segment-disjointness of the remaining consecutive edges from the query segment `q—q'`. -/
lemma chainSegDisjoint_tail (q q' a : ℝ × ℝ) (L : List (ℝ × ℝ))
    (h : chainSegDisjoint q q' (a :: L)) : chainSegDisjoint q q' L := by
  cases L with
  | nil => trivial
  | cons b rest => exact ((chainSegDisjoint_cons₂ q q' a b rest).mp h).2

/-- **`chainSegDisjoint` is inherited by every suffix `L.drop n`.** A suffix of a polyline keeps
all its consecutive edges (they are consecutive edges of the whole), so segment-disjointness is
preserved. Used to extract the suffix hypothesis `chainSegDisjoint q q' (c :: rest)` required by
`chainWind_arc_cross_one_vertex` from a single global disjointness hypothesis. -/
lemma chainSegDisjoint_drop (q q' : ℝ × ℝ) (n : ℕ) :
    ∀ (L : List (ℝ × ℝ)), chainSegDisjoint q q' L → chainSegDisjoint q q' (L.drop n) := by
  induction n with
  | zero => intro L h; simpa using h
  | succ k ih =>
    intro L h
    cases L with
    | nil => simpa using h
    | cons a rest =>
      rw [List.drop_succ_cons]
      exact ih rest (chainSegDisjoint_tail q q' a rest h)

/-- **`chainSegDisjoint` is inherited by every prefix `L.take n`.** A prefix of a polyline keeps
all its consecutive edges, so segment-disjointness is preserved. Used to extract the prefix
hypothesis `chainSegDisjoint q q' (front ++ [a])` required by `chainWind_arc_cross_one_vertex`
from a single global disjointness hypothesis. -/
lemma chainSegDisjoint_take (q q' : ℝ × ℝ) :
    ∀ (L : List (ℝ × ℝ)) (n : ℕ),
      chainSegDisjoint q q' L → chainSegDisjoint q q' (L.take n)
  | [], n, h => by simpa using h
  | [a], n, h => by cases n with | zero => trivial | succ k => simpa using h
  | a :: b :: rest, n, h => by
    cases n with
    | zero => trivial
    | succ k =>
      cases k with
      | zero => show chainSegDisjoint q q' [a]; trivial
      | succ m =>
        rw [chainSegDisjoint_cons₂] at h
        have ih := chainSegDisjoint_take q q' (b :: rest) (m + 1) h.2
        rw [show (a :: b :: rest).take (m + 2) = a :: (b :: rest).take (m + 1) by simp [List.take]]
        cases hbr : (b :: rest).take (m + 1) with
        | nil => rw [List.take_succ_cons] at hbr; simp at hbr
        | cons x xs =>
          rw [chainSegDisjoint_cons₂]
          refine ⟨?_, ?_⟩
          · have hx : x = b := by
              rw [List.take_succ_cons] at hbr; injection hbr with h1 _; exact h1.symm
            rw [hx]; exact h.1
          · rw [← hbr]; exact ih

/-- **`chainWind` transport across one arc vertex, from a single global disjointness hypothesis.**
Convenience repackaging of `chainWind_arc_cross_one_vertex`: instead of separate prefix/suffix
`chainSegDisjoint` hypotheses and the flanking height-avoidances, it suffices to supply
*one* `chainSegDisjoint q q'` for the corner list with the crossed vertex `v_{i+k}` **removed**
(`front ++ a :: c :: rest`), together with both endpoints being off the vertex height and the two
chord-disjointness conditions `[a, v_{i+k}]`, `[v_{i+k}, c]`. The prefix `front ++ [a]`, the suffix
`c :: rest`, and the flanking corner-height avoidances `p.2 ≠ a.2`, `p.2 ≠ c.2` are all extracted
from that single hypothesis using `chainSegDisjoint_take`/`chainSegDisjoint_drop` (a prefix, a
suffix, and the head pair-condition of the middle edge `a → c`). This is the form a height-monotone
transport invokes when it has already verified segment-disjointness from every chord *except* the
two incident to the single vertex it is about to cross. -/
lemma chainWind_arc_cross_one_vertex_global (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (k : ℕ) (hk1 : 1 ≤ k) (hkd : k ≤ d) (q q' : ℝ × ℝ)
    {front rest : List (ℝ × ℝ)} {a c : ℝ × ℝ}
    (hsplit : arcCorners P y i d
      = front ++ a :: toReal (P.vert (i + (k : ZMod P.n))) :: c :: rest)
    (hglob : chainSegDisjoint q q' (front ++ a :: c :: rest))
    (hqb : q.2 ≠ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (hq'b : q'.2 ≠ (toReal (P.vert (i + (k : ZMod P.n)))).2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a (toReal (P.vert (i + (k : ZMod P.n)))))
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ (toReal (P.vert (i + (k : ZMod P.n)))) c) :
    chainWind (arcCorners P y i d) q = chainWind (arcCorners P y i d) q' := by
  have hfront : chainSegDisjoint q q' (front ++ [a]) := by
    have := chainSegDisjoint_take q q' (front ++ a :: c :: rest) (front.length + 1) hglob
    rwa [show (front ++ a :: c :: rest).take (front.length + 1) = front ++ [a] from by
      simp [List.take_append]] at this
  have hrest : chainSegDisjoint q q' (c :: rest) := by
    have := chainSegDisjoint_drop q q' (front.length + 1) (front ++ a :: c :: rest) hglob
    rwa [show (front ++ a :: c :: rest).drop (front.length + 1) = c :: rest from by
      rw [List.drop_append]; simp] at this
  have hpair := chainSegDisjoint_drop q q' front.length (front ++ a :: c :: rest) hglob
  rw [show (front ++ a :: c :: rest).drop front.length = a :: c :: rest from by
    rw [List.drop_append]; simp, chainSegDisjoint_cons₂] at hpair
  exact chainWind_arc_cross_one_vertex P y i d k hk1 hkd q q' hsplit hfront hpair.1.1 hqb hq'b
    hpair.1.2.1 hsab hscb hrest

/-- A predicate stating that every consecutive chord `[a, b]` of the polyline `pts` is disjoint
from the query segment `q—q'`. The chord-only part of `chainSegDisjoint` (no endpoint-height
avoidance), used by the single-height transport which permits the shared height `h` to be crossed
and so cannot demand height-avoidance at the `h`-vertices. -/
def chainChordDisjoint (q q' : ℝ × ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b) ∧ chainChordDisjoint q q' (b :: rest)

lemma chainChordDisjoint_cons₂ (q q' a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    chainChordDisjoint q q' (a :: b :: rest) ↔
      (∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b) ∧ chainChordDisjoint q q' (b :: rest) :=
  Iff.rfl

lemma chainChordDisjoint_tail (q q' a : ℝ × ℝ) (L : List (ℝ × ℝ))
    (h : chainChordDisjoint q q' (a :: L)) : chainChordDisjoint q q' L := by
  cases L with
  | nil => trivial
  | cons b rest => exact ((chainChordDisjoint_cons₂ q q' a b rest).mp h).2

/-- A predicate stating that no two *consecutive* vertices of the polyline `pts` both sit at the
height `h`. Equivalently, the `h`-vertices are isolated, so each is flanked by off-`h` corners and
the single-height transport can pair its two incident chords for cancellation. -/
def noAdjAtHeight (h : ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => ¬ (a.2 = h ∧ b.2 = h) ∧ noAdjAtHeight h (b :: rest)

lemma noAdjAtHeight_cons₂ (h : ℝ) (a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    noAdjAtHeight h (a :: b :: rest) ↔
      ¬ (a.2 = h ∧ b.2 = h) ∧ noAdjAtHeight h (b :: rest) := Iff.rfl

/-- **`chainWind` transport across exactly one shared vertex-height value `h` (the multi-vertex
crossing engine).** Along a query segment `q—q'` that is disjoint from every chord of the polyline
(`chainChordDisjoint`), suppose each vertex either has its height avoided by the whole segment
(`∀ p ∈ [q,q'], p.2 ≠ v.2` — the off-interval vertices) or sits exactly at the single crossed height
`h` (`v.2 = h`), the head vertex is off `h`, no two consecutive vertices are both at `h`, and both
endpoints are off `h` (`q.2 ≠ h`, `q'.2 ≠ h`). Then the open-polyline winding is unchanged from `q`
to `q'`. Proof by strong induction on the length: each edge whose *next* vertex is off `h` is
individually constant (`edgeWind_eq_of_seg_disjoint`); when the next vertex `b` sits at `h` it is
interior (head off `h`, no adjacent `h`-vertex), so the incoming/outgoing pair `a→b→c` is transported
together with cancellation (`edgeWind_pair_eq_of_seg_disjoint`), absorbing the `h` crossing, and the
recursion continues from the off-`h` corner `c`. This realises the prompt's KEY MATH: chords not
incident to height `h` are constant, and at each `h`-vertex the two incident chords' flips cancel. -/
lemma chainWind_cross_one_height_aux (h : ℝ) (q q' : ℝ × ℝ)
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h) :
    ∀ (n : ℕ) (pts : List (ℝ × ℝ)), pts.length ≤ n →
      chainChordDisjoint q q' pts →
      (∀ v ∈ pts, (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h) →
      (∀ a ∈ pts.head?, a.2 ≠ h) →
      (∀ a ∈ pts.getLast?, a.2 ≠ h) →
      noAdjAtHeight h pts →
      chainWind pts q = chainWind pts q' := by
  intro n
  induction n with
  | zero =>
    intro pts hlen _ _ _ _ _
    rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen; rfl
  | succ n ih =>
    intro pts hlen hchord hheights hhead hlast hchain
    match pts with
    | [] => rfl
    | [a] => rfl
    | a :: b :: rest =>
      -- head a is off h
      have hah : a.2 ≠ h := hhead a (by simp)
      rw [chainChordDisjoint_cons₂] at hchord
      by_cases hbh : b.2 = h
      · -- b sits at the crossed height: pair a→b→c (c is off h by no-adjacency), then recurse on c::rest
        match rest with
        | [] =>
          -- b is the last vertex; `hlast` forces b off h, contradicting hbh.
          exact absurd (hlast b (by simp)) (by rw [hbh]; simp)
        | c :: rest' =>
          rw [noAdjAtHeight_cons₂, noAdjAtHeight_cons₂] at hchain
          have hch : c.2 ≠ h := by
            intro hcc; exact hchain.2.1 ⟨hbh, hcc⟩
          have hac : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2 := by
            rcases hheights a (by simp) with hcase | hcase
            · exact hcase
            · exact absurd hcase hah
          have hcc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2 := by
            rcases hheights c (by simp) with hcase | hcase
            · exact hcase
            · exact absurd hcase hch
          have hsab := hchord.1
          have hscb := (chainChordDisjoint_cons₂ q q' b c rest').mp hchord.2 |>.1
          have hpair := edgeWind_pair_eq_of_seg_disjoint a b c q q' hac hcc
            (by rw [hbh]; exact hqh) (by rw [hbh]; exact hq'h) hsab hscb
          -- recurse on c :: rest'
          have hrec : chainWind (c :: rest') q = chainWind (c :: rest') q' := by
            apply ih (c :: rest') (by simp at hlen ⊢; omega)
            · exact (chainChordDisjoint_cons₂ q q' b c rest').mp hchord.2 |>.2
            · intro v hv; exact hheights v (by simp [hv])
            · intro x hx; simp only [List.head?_cons, Option.mem_some_iff] at hx;
              rw [← hx]; exact hch
            · intro x hx
              apply hlast x
              rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
              exact hx
            · exact hchain.2.2
          rw [chainWind_cons₂, chainWind_cons₂, chainWind_cons₂, chainWind_cons₂]
          rw [hrec] at *
          linarith [hpair]
      · -- b off h: edge a→b is individually constant; recurse on b::rest
        have hab : ∀ p ∈ segment ℝ q q', p.2 ≠ b.2 := by
          rcases hheights b (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hbh
        have hac : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2 := by
          rcases hheights a (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hah
        have hedge := edgeWind_eq_of_seg_disjoint a b q q' hac hab hchord.1
        have hrec : chainWind (b :: rest) q = chainWind (b :: rest) q' := by
          apply ih (b :: rest) (by simp at hlen ⊢; omega) hchord.2
          · intro v hv; exact hheights v (by simp [hv])
          · intro x hx; simp only [List.head?_cons, Option.mem_some_iff] at hx;
            rw [← hx]; exact hbh
          · intro x hx
            apply hlast x
            rw [List.getLast?_cons_cons]
            exact hx
          · rw [noAdjAtHeight_cons₂] at hchain; exact hchain.2
        rw [chainWind_cons₂, chainWind_cons₂, hedge, hrec]

/-- **`chainWind` transport across exactly one shared vertex-height value `h`.** Public form of
`chainWind_cross_one_height_aux` (the length-fuel is supplied automatically as `pts.length`): along
a query segment `q—q'` disjoint from every chord (`chainChordDisjoint`), with each vertex either at
height `h` or having its height avoided by the whole segment, both list endpoints off `h`, the
endpoints `q`, `q'` off `h`, and no two consecutive vertices both at `h` (`noAdjAtHeight`), the
open-polyline winding is unchanged. -/
lemma chainWind_cross_one_height (h : ℝ) (q q' : ℝ × ℝ) (pts : List (ℝ × ℝ))
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h)
    (hchord : chainChordDisjoint q q' pts)
    (hheights : ∀ v ∈ pts, (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h)
    (hhead : ∀ a ∈ pts.head?, a.2 ≠ h)
    (hlast : ∀ a ∈ pts.getLast?, a.2 ≠ h)
    (hnoadj : noAdjAtHeight h pts) :
    chainWind pts q = chainWind pts q' :=
  chainWind_cross_one_height_aux h q q' hqh hq'h pts.length pts le_rfl hchord hheights hhead hlast
    hnoadj

/-- **`loopWind` transport across exactly one shared arc-vertex height `h`, above `y`.** Loop-level
form of `chainWind_cross_one_height` for the crossing-arc corner list `arcCorners P y i d`: along a
query segment `q—q'` lying weakly above `y`, disjoint from every arc chord, with each arc corner
either at height `h` or having its height avoided by the whole segment, the two threshold corners
off `h`, the endpoints `q`, `q'` off `h`, and no two consecutive arc corners both at `h`, the loop
winding is unchanged. The horizontal return edge (height `y`) contributes nothing at either endpoint
(`loopWind_eq_chainWind_of_above`), so only the open arc matters, and that is constant by
`chainWind_cross_one_height`. This lifts the single-height crossing engine to `loopWind`, the form a
height-monotone climbing leg invokes when it crosses one shared arc-vertex height. -/
lemma loopWind_cross_one_height_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (h : ℝ) (q q' : ℝ × ℝ) (hq : y ≤ q.2) (hq' : y ≤ q'.2)
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h)
    (hchord : chainChordDisjoint q q' (arcCorners P y i d))
    (hheights : ∀ v ∈ arcCorners P y i d,
      (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h)
    (hhead : ∀ a ∈ (arcCorners P y i d).head?, a.2 ≠ h)
    (hlast : ∀ a ∈ (arcCorners P y i d).getLast?, a.2 ≠ h)
    (hnoadj : noAdjAtHeight h (arcCorners P y i d)) :
    loopWind P y i d q = loopWind P y i d q' := by
  rw [loopWind_eq_chainWind_of_above P y i d q hq,
    loopWind_eq_chainWind_of_above P y i d q' hq']
  exact chainWind_cross_one_height h q q' (arcCorners P y i d) hqh hq'h hchord hheights hhead hlast
    hnoadj

/-- **Minimum element of a list satisfying a decidable predicate.** If some element of `L`
satisfies `P`, there is a `P`-element `h ∈ L` that is `≤` every `P`-element of `L`. The
finite-extremum tool for picking the *lowest* crossed arc-vertex height in the monotone-transport
induction. -/
lemma exists_min_pred {L : List ℝ} {P : ℝ → Prop} [DecidablePred P] (hL : ∃ x ∈ L, P x) :
    ∃ h ∈ L, P h ∧ ∀ v ∈ L, P v → h ≤ v := by
  classical
  have hne : (L.filter (fun v => P v)) ≠ [] := by
    obtain ⟨x, hx, hPx⟩ := hL
    intro hc; rw [List.filter_eq_nil_iff] at hc; exact hc x hx (by simpa using hPx)
  have hmn : (L.filter (fun v => P v)).min? ≠ none := by rw [Ne, List.min?_eq_none_iff]; exact hne
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hmn
  rw [List.min?_eq_some_iff] at hm
  obtain ⟨hmem, hmin⟩ := hm
  rw [List.mem_filter] at hmem
  refine ⟨m, hmem.1, by simpa using hmem.2, fun v hv hPv => ?_⟩
  exact hmin v (List.mem_filter.mpr ⟨hv, by simpa using hPv⟩)

/-- **`chainChordDisjoint` is monotone under shrinking the query segment.** If the chord-avoidance
holds along `q—q'` and `[q, m] ⊆ [q, q']`, it holds along the sub-segment `q—m`. The transport
restriction lemma used to push the chord hypotheses onto the two split pieces of a monotone leg. -/
lemma chainChordDisjoint_of_subset {q q' a b : ℝ × ℝ} {pts : List (ℝ × ℝ)}
    (hsub : segment ℝ a b ⊆ segment ℝ q q') (h : chainChordDisjoint q q' pts) :
    chainChordDisjoint a b pts := by
  induction pts with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest' =>
      rw [chainChordDisjoint_cons₂] at h ⊢
      exact ⟨fun p hp => h.1 p (hsub hp), ih h.2⟩

/-- **`chainSegDisjoint` is monotone under shrinking the query segment.** Restriction of the full
segment-disjointness (heights *and* chords avoided) to a sub-segment `[q, m] ⊆ [q, q']`. -/
lemma chainSegDisjoint_of_subset {q q' m : ℝ × ℝ} {pts : List (ℝ × ℝ)}
    (hsub : segment ℝ q m ⊆ segment ℝ q q') (h : chainSegDisjoint q q' pts) :
    chainSegDisjoint q m pts := by
  induction pts with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest' =>
      rw [chainSegDisjoint_cons₂] at h ⊢
      refine ⟨⟨fun p hp => h.1.1 p (hsub hp), fun p hp => h.1.2.1 p (hsub hp),
        fun p hp => h.1.2.2 p (hsub hp)⟩, ih h.2⟩

/-- **Height range of a segment.** Every point of `[q, q']` has height between `min q.2 q'.2`
and `max q.2 q'.2`. A heightwise enclosure of the segment, used to certify that a height
strictly outside the segment's height span is never attained along it. -/
lemma segment_height_mem (q q' p : ℝ × ℝ) (hp : p ∈ segment ℝ q q') :
    min q.2 q'.2 ≤ p.2 ∧ p.2 ≤ max q.2 q'.2 := by
  obtain ⟨s, t, hs, ht, hst, hpt⟩ := hp
  have hh : p.2 = s * q.2 + t * q'.2 := by rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
  refine ⟨?_, ?_⟩
  · rw [hh]
    have h1 := mul_le_mul_of_nonneg_left (min_le_left q.2 q'.2) hs
    have h2 := mul_le_mul_of_nonneg_left (min_le_right q.2 q'.2) ht
    have he : s * min q.2 q'.2 + t * min q.2 q'.2 = min q.2 q'.2 := by
      linear_combination (min q.2 q'.2) * hst
    linarith
  · rw [hh]
    have h1 := mul_le_mul_of_nonneg_left (le_max_left q.2 q'.2) hs
    have h2 := mul_le_mul_of_nonneg_left (le_max_right q.2 q'.2) ht
    have he : s * max q.2 q'.2 + t * max q.2 q'.2 = max q.2 q'.2 := by
      linear_combination (max q.2 q'.2) * hst
    linarith

/-- **From chord-disjointness plus full height-avoidance to `chainSegDisjoint`.** If the query
segment avoids the height of *every* corner of the polyline and is disjoint from every chord, then
each consecutive edge meets the full `chainSegDisjoint` condition. The bridge used in the base case
(no crossed height) of the monotone-transport induction. -/
lemma chainSegDisjoint_of_chord_and_heights {q q' : ℝ × ℝ} {pts : List (ℝ × ℝ)}
    (hchord : chainChordDisjoint q q' pts)
    (hh : ∀ v ∈ pts, ∀ p ∈ segment ℝ q q', p.2 ≠ v.2) :
    chainSegDisjoint q q' pts := by
  induction pts with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest' =>
      rw [chainChordDisjoint_cons₂] at hchord
      refine ⟨⟨fun p hp => hh a (by simp) p hp, fun p hp => hh b (by simp) p hp, hchord.1⟩,
        ih hchord.2 (fun v hv => hh v (by simp [hv]))⟩

/-- **Strict drop of a filter length under a strict sub-predicate.** If `P₂ v → P₁ v` for every
`v ∈ L` and some witness `w ∈ L` has `P₁ w` but not `P₂ w`, then the `P₂`-filtered length is
strictly below the `P₁`-filtered length. The decreasing measure for the upper piece in the
monotone-transport induction (it loses at least the lowest crossed height). -/
lemma length_filter_lt_of_strict {α : Type*} (L : List α) (P₁ P₂ : α → Bool)
    (hsub : ∀ v ∈ L, P₂ v → P₁ v) (w : α) (hw : w ∈ L) (hw1 : P₁ w) (hw2 : ¬ P₂ w) :
    (L.filter P₂).length < (L.filter P₁).length := by
  induction L with
  | nil => simp at hw
  | cons a t ih =>
    have hmono : ∀ (s : List α), (∀ v ∈ s, P₂ v → P₁ v) →
        (s.filter P₂).length ≤ (s.filter P₁).length := by
      intro s hs
      induction s with
      | nil => simp
      | cons b u ihu =>
        simp only [List.filter_cons]
        by_cases hb2 : P₂ b = true
        · rw [if_pos hb2, if_pos (hs b (by simp) hb2)]; simp
          exact ihu (fun v hv => hs v (by simp [hv]))
        · rw [if_neg hb2]
          by_cases hb1 : P₁ b = true
          · rw [if_pos hb1]; simp; have := ihu (fun v hv => hs v (by simp [hv])); omega
          · rw [if_neg hb1]; exact ihu (fun v hv => hs v (by simp [hv]))
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hw with rfl | hwt
    · rw [if_neg (by simpa using hw2), if_pos hw1]
      simp only [List.length_cons]
      have := hmono t (fun v hv => hsub v (by simp [hv])); omega
    · by_cases ha2 : P₂ a = true
      · rw [if_pos ha2, if_pos (hsub a (by simp) ha2)]; simp
        exact ih (fun v hv => hsub v (by simp [hv])) hwt
      · rw [if_neg ha2]
        by_cases ha1 : P₁ a = true
        · rw [if_pos ha1]; simp; have := ih (fun v hv => hsub v (by simp [hv])) hwt; omega
        · rw [if_neg ha1]; exact ih (fun v hv => hsub v (by simp [hv])) hwt

/-- **Auxiliary (fuel) form of monotone-above transport.** Strong induction on a length-fuel
bounding the number of arc corners (with multiplicity) whose height lies strictly between the two
endpoints. -/
lemma loopWind_eq_of_monotone_above_aux (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hnoadj : ∀ h : ℝ, noAdjAtHeight h (arcCorners P y i d)) :
    ∀ (n : ℕ) (q q' : ℝ × ℝ),
      ((arcCorners P y i d).filter
        (fun v => decide (q.2 < v.2 ∧ v.2 < q'.2))).length ≤ n →
      y ≤ q.2 → q.2 < q'.2 →
      chainChordDisjoint q q' (arcCorners P y i d) →
      (∀ v ∈ arcCorners P y i d, q.2 ≠ v.2 ∧ q'.2 ≠ v.2) →
      loopWind P y i d q = loopWind P y i d q' := by
  classical
  intro n
  induction n with
  | zero =>
    intro q q' hlen hq hmono hchord hoff
    -- no corner height in (q.2, q'.2): segment fully avoids all corner heights ⟹ seg-disjoint
    rw [Nat.le_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff] at hlen
    have hseg : chainSegDisjoint q q' (arcCorners P y i d) := by
      apply chainSegDisjoint_of_chord_and_heights hchord
      intro v hv p hp hpv
      have hrange := segment_height_mem q q' p hp
      rw [min_eq_left (le_of_lt hmono), max_eq_right (le_of_lt hmono)] at hrange
      have hne := hoff v hv
      have hl := hlen v hv
      simp only [decide_eq_true_eq, not_and, not_lt] at hl
      rcases lt_or_eq_of_le hrange.1 with h1 | h1
      · rcases lt_or_eq_of_le hrange.2 with h2 | h2
        · rw [hpv] at h1 h2; exact absurd (hl h1) (by linarith)
        · rw [hpv] at h2; exact hne.2 h2.symm
      · rw [hpv] at h1; exact hne.1 h1
    exact loopWind_eq_of_seg_disjoint_above P y i d q q' hq
      (le_of_lt (lt_of_le_of_lt hq hmono)) hseg
  | succ n ih =>
    intro q q' hlen hq hmono hchord hoff
    by_cases hex : ∃ v ∈ arcCorners P y i d, q.2 < v.2 ∧ v.2 < q'.2
    · -- there is a crossed corner height; split at a generic height just above the lowest one
      -- lowest crossed corner height `h`
      obtain ⟨h, hhmem, ⟨hhlo, hhhi⟩, hhmin⟩ :=
        exists_min_pred (L := (arcCorners P y i d).map Prod.snd)
          (P := fun t => q.2 < t ∧ t < q'.2)
          (by obtain ⟨v, hv, hvlo, hvhi⟩ := hex
              exact ⟨v.2, List.mem_map_of_mem hv, hvlo, hvhi⟩)
      -- candidate next heights: corner heights in (h, q'.2), plus the sentinel q'.2
      set cand : List ℝ :=
        ((arcCorners P y i d).map Prod.snd).filter (fun t => decide (h < t ∧ t < q'.2)) ++ [q'.2]
        with hcand
      have hcand_ne : cand ≠ [] := by rw [hcand]; simp
      have hcand_gt : ∀ t ∈ cand, h < t := by
        intro t ht
        rw [hcand, List.mem_append] at ht
        rcases ht with ht | ht
        · rw [List.mem_filter] at ht; exact (by simpa using ht.2 : h < t ∧ t < q'.2).1
        · simp only [List.mem_singleton] at ht; rw [ht]; linarith
      -- minimum of cand
      have hmn : cand.min? ≠ none := by
        rw [Ne, List.min?_eq_none_iff]; exact hcand_ne
      obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hmn
      rw [List.min?_eq_some_iff] at hm'
      obtain ⟨hm'mem, hm'min⟩ := hm'
      have hhm' : h < m' := hcand_gt m' hm'mem
      have hm'leq' : m' ≤ q'.2 := hm'min q'.2 (by rw [hcand]; simp)
      set h' : ℝ := (h + m') / 2 with hh'def
      have hh'lo : h < h' := by rw [hh'def]; linarith
      have hh'hi : h' < m' := by rw [hh'def]; linarith
      have hh'q' : h' < q'.2 := lt_of_lt_of_le hh'hi hm'leq'
      have hqh' : q.2 < h' := lt_trans hhlo hh'lo
      -- no corner height lies in (q.2, h')  except value exactly h
      have hno_between : ∀ v ∈ arcCorners P y i d, h < v.2 → v.2 < q'.2 → h' ≤ v.2 := by
        intro v hv hvlo hvhi
        have : v.2 ∈ cand := by
          rw [hcand, List.mem_append]; left
          rw [List.mem_filter]
          exact ⟨List.mem_map_of_mem hv, by simpa using ⟨hvlo, hvhi⟩⟩
        exact le_trans (le_of_lt hh'hi) (hm'min v.2 this)
      -- no corner at exactly height h'
      have hno_h' : ∀ v ∈ arcCorners P y i d, v.2 ≠ h' := by
        intro v hv hcontra
        have hvlo : h < v.2 := by rw [hcontra]; exact hh'lo
        have hvhi : v.2 < q'.2 := by rw [hcontra]; exact hh'q'
        have hmem : v.2 ∈ cand := by
          rw [hcand, List.mem_append]; left
          rw [List.mem_filter]
          exact ⟨List.mem_map_of_mem hv, by simpa using ⟨hvlo, hvhi⟩⟩
        have := hm'min v.2 hmem
        rw [hcontra] at this; linarith
      -- split the segment at height h'
      obtain ⟨mpt, hmpt_mem, hmpt2, hsub1, hsub2, hle1, hge2⟩ :=
        segment_split_at_height hmono hqh' hh'q'
      -- LOWER piece [q, mpt]: crosses exactly the single height h
      have hlow : loopWind P y i d q = loopWind P y i d mpt := by
        apply loopWind_cross_one_height_above P y i d h q mpt hq (by rw [hmpt2]; linarith)
          (ne_of_lt hhlo) (by rw [hmpt2]; exact ne_of_gt hh'lo)
          (chainChordDisjoint_of_subset hsub1 hchord)
        · -- heights condition: each corner is off [q,mpt] height, or equals h
          intro v hv
          by_cases hvh : v.2 = h
          · exact Or.inr hvh
          · left
            intro p hp hpv
            have hple : p.2 ≤ h' := hle1 p hp
            have hpge : q.2 ≤ p.2 := by
              have := (segment_height_mem q mpt p hp).1
              rwa [min_eq_left (by rw [hmpt2]; linarith)] at this
            have hoffv := hoff v hv
            -- p.2 = v.2 with q.2 ≤ v.2 ≤ h'; corners in this band are only at h
            rw [hpv] at hple hpge
            rcases lt_or_eq_of_le hpge with hlt | heq
            · -- q.2 < v.2 ≤ h'
              rcases lt_or_eq_of_le hple with hlt2 | heq2
              · -- q.2 < v.2 < h' < q'.2: by minimality of h, v.2 ≥ h; not = h ⟹ h < v.2 < q'.2 ⟹ h' ≤ v.2
                have hvq' : v.2 < q'.2 := lt_trans hlt2 hh'q'
                have hge_h : h ≤ v.2 := hhmin v.2 (List.mem_map_of_mem hv) ⟨hlt, hvq'⟩
                have hvgt : h < v.2 := lt_of_le_of_ne hge_h (Ne.symm hvh)
                have := hno_between v hv hvgt hvq'
                linarith
              · exact hno_h' v hv heq2
            · exact hoffv.1 heq
        · -- head off h
          intro a ha
          have ha2 : a.2 = y := by
            simp only [arcCorners, List.head?_cons, Option.mem_some_iff] at ha
            rw [← ha]
          rw [ha2]; exact ne_of_lt (lt_of_le_of_lt hq hhlo)
        · -- last off h
          intro a ha
          have ha2 : a.2 = y := by
            have hL : (arcCorners P y i d).getLast? = some (P.edgeThr y (i + (d : ZMod P.n)), y) := by
              unfold arcCorners
              rw [List.getLast?_cons, List.getLast?_concat]; rfl
            rw [hL, Option.mem_some_iff] at ha; rw [← ha]
          rw [ha2]; exact ne_of_lt (lt_of_le_of_lt hq hhlo)
        · exact hnoadj h
      -- UPPER piece [mpt, q']: one fewer crossed corner ⟹ IH
      have hupp : loopWind P y i d mpt = loopWind P y i d q' := by
        apply ih mpt q' ?_ (by rw [hmpt2]; linarith) ?_
          (chainChordDisjoint_of_subset hsub2 hchord) ?_
        · -- count drop
          have hwit : ∃ v ∈ arcCorners P y i d, v.2 = h := by
            obtain ⟨v, hv, hv2⟩ := List.mem_map.mp hhmem
            exact ⟨v, hv, hv2⟩
          obtain ⟨vh, hvh_mem, hvh2⟩ := hwit
          have hdrop := length_filter_lt_of_strict (arcCorners P y i d)
            (fun v => decide (q.2 < v.2 ∧ v.2 < q'.2))
            (fun v => decide (mpt.2 < v.2 ∧ v.2 < q'.2))
            (by intro v _ hv2
                simp only [decide_eq_true_eq] at hv2 ⊢
                rw [hmpt2] at hv2
                exact ⟨lt_trans hqh' hv2.1, hv2.2⟩)
            vh hvh_mem
            (by simp only [decide_eq_true_eq]; rw [hvh2]; exact ⟨hhlo, hhhi⟩)
            (by simp only [decide_eq_true_eq, not_and, not_lt]
                intro hlt; rw [hmpt2] at hlt; rw [hvh2] at hlt; linarith)
          omega
        · rw [hmpt2]; exact hh'q'
        · intro v hv
          refine ⟨?_, (hoff v hv).2⟩
          rw [hmpt2]
          exact fun hc => hno_h' v hv hc.symm
      rw [hlow, hupp]
    · -- no crossed corner height: the whole monotone segment avoids all corner heights
      simp only [not_exists, not_and, not_lt] at hex
      have hseg : chainSegDisjoint q q' (arcCorners P y i d) := by
        apply chainSegDisjoint_of_chord_and_heights hchord
        intro v hv p hp hpv
        have hrange := segment_height_mem q q' p hp
        rw [min_eq_left (le_of_lt hmono), max_eq_right (le_of_lt hmono)] at hrange
        have hne := hoff v hv
        rcases lt_or_eq_of_le hrange.1 with h1 | h1
        · rcases lt_or_eq_of_le hrange.2 with h2 | h2
          · rw [hpv] at h1 h2; exact absurd (hex v hv h1) (by linarith)
          · rw [hpv] at h2; exact hne.2 h2.symm
        · rw [hpv] at h1; exact hne.1 h1
      exact loopWind_eq_of_seg_disjoint_above P y i d q q' hq
        (le_of_lt (lt_of_le_of_lt hq hmono)) hseg

/-- **Monotone-above transport of `loopWind` (STEP 1).** Let `q—q'` be a *height-strictly-monotone*
segment lying weakly above `y` (`y ≤ q.2`, `y ≤ q'.2`, `q.2 ≠ q'.2`), disjoint from every arc chord
(`chainChordDisjoint`), with *both* endpoints off the height of every arc corner. If no two
consecutive arc corners share a height (`noAdjAtHeight h` for every `h`), then `loopWind P y i d`
takes the same value at `q` and `q'`. Proof by strong induction (`loopWind_eq_of_monotone_above_aux`)
on the number of arc corners crossed in height: with none crossed the segment is fully
`chainSegDisjoint`; otherwise split just above the lowest crossed height `h`, transport the lower
piece across exactly the single height `h` (`loopWind_cross_one_height_above`) and the upper piece
(one fewer crossed height) by induction. The winding equation is symmetric in `q`, `q'`, so both
monotone directions are covered. -/
lemma loopWind_eq_of_monotone_above (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (hnoadj : ∀ h : ℝ, noAdjAtHeight h (arcCorners P y i d))
    (q q' : ℝ × ℝ) (hq : y ≤ q.2) (hq' : y ≤ q'.2) (hne : q.2 ≠ q'.2)
    (hchord : chainChordDisjoint q q' (arcCorners P y i d))
    (hoff : ∀ v ∈ arcCorners P y i d, q.2 ≠ v.2 ∧ q'.2 ≠ v.2) :
    loopWind P y i d q = loopWind P y i d q' := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact loopWind_eq_of_monotone_above_aux P y i d hnoadj _ q q' le_rfl hq hlt hchord hoff
  · -- swap endpoints: the equation is symmetric
    refine (loopWind_eq_of_monotone_above_aux P y i d hnoadj _ q' q le_rfl hq' hgt ?_ ?_).symm
    · exact chainChordDisjoint_of_subset (a := q') (b := q) (by rw [segment_symm]) hchord
    · intro v hv; exact ⟨(hoff v hv).2, (hoff v hv).1⟩

/-- **Dropping the head of a horizontal-leading pair leaves `chainWind` invariant.** When the
first edge `a→b` of the polyline is horizontal (`a.2 = b.2`), its `edgeWind` contribution is `0`
(`edgeWind_eq_zero_of_eq_height`), so the open-polyline winding of `a :: b :: rest` equals that of
`b :: rest`. This is the *collapse* step of the prompt's plan, applied at the head: a horizontal
edge can be removed without changing `chainWind`, because no reconnection edge is needed (the head
edge is the only one touched and it contributes nothing). Iterating this from the head removes a
horizontal run that *starts* the list; combined with `chainWind_cons₂` it underlies the
height-collapse normalisation that makes a polyline `noAdjAtHeight`-clean at any given height. -/
lemma chainWind_drop_head_of_eq_height (a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) (q : ℝ × ℝ)
    (h : a.2 = b.2) : chainWind (a :: b :: rest) q = chainWind (b :: rest) q := by
  rw [chainWind_cons₂, edgeWind_eq_zero_of_eq_height a b q h, zero_add]

/-- **Split-middle pair constancy from segment disjointness, non-crossing branch.** Two
*independent* consecutive edges `a→b₁` (entering a height-`h` run) and `b₂→c` (leaving it), with
the query segment `q—q'` avoiding all four endpoint heights and disjoint from both chord segments
`[a,b₁]`, `[b₂,c]`, contribute the same combined `edgeWind` at `q` and `q'`. Each edge is
*individually* constant by `edgeWind_eq_of_seg_disjoint` (the segment avoids the relevant endpoint
heights and stays off the chord), so no cancellation is needed. This is the non-crossing branch of
the horizontal-run transport (`b₁.2 = b₂.2 = h` and the segment stays on one side of `h`); it is
the split-middle analogue of `edgeWind_pair_eq_of_seg_disjoint_off_mid`, where the middle vertex
is replaced by the two distinct run endpoints `b₁`, `b₂`. -/
lemma edgeWind_split_pair_eq_of_seg_disjoint_off_mid (a b1 b2 c q q' : ℝ × ℝ)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hob1 : ∀ p ∈ segment ℝ q q', p.2 ≠ b1.2)
    (hob2 : ∀ p ∈ segment ℝ q q', p.2 ≠ b2.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hsab1 : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b1)
    (hsb2c : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b2 c) :
    edgeWind a b1 q + edgeWind b2 c q = edgeWind a b1 q' + edgeWind b2 c q' := by
  rw [edgeWind_eq_of_seg_disjoint a b1 q q' hoa hob1 hsab1,
      edgeWind_eq_of_seg_disjoint b2 c q q' hob2 hoc hsb2c]


set_option maxHeartbeats 1600000 in
/-- **Split-middle cancellation of the ray-crossing winding across a horizontal run.** Generalises
`edgeWind_pair_cross` from a single shared vertex `b` to two distinct run endpoints `b1`, `b2` sharing
the same height (`b1.2 = b2.2`). For the entering edge `a→b1` and the leaving edge `b2→c`, a query
segment `hi—lo` straddling the run height (`b1.2 ≤ hi.2`, `lo.2 < b1.2`) that avoids the outer heights
`a.2`, `c.2`, avoids both cross-loci and both chord segments `[a,b1]`, `[b2,c]`, and whose crossing
point at height `b1.2` lies in a column *outside* the run's x-span (so `(b1.1 - p.1)` and `(b2.1 - p.1)`
have the same sign — the hypothesis `hcol`), keeps the combined contribution unchanged. The two flips
of `edgeWind a b1` and `edgeWind b2 c` across the crossing cancel exactly when the crossing column is
off the run span; this is the horizontal-run analogue of the shared-vertex cancellation. -/
lemma edgeWind_split_pair_cross (a b1 b2 c hi lo : ℝ × ℝ)
    (hb : b1.2 = b2.2)
    (hoa : ∀ p ∈ segment ℝ hi lo, p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ hi lo, p.2 ≠ c.2)
    (hcab : ∀ p ∈ segment ℝ hi lo, cross (b1 - a) (p - a) ≠ 0)
    (hccb : ∀ p ∈ segment ℝ hi lo, cross (c - b2) (p - b2) ≠ 0)
    (hsab : ∀ p ∈ segment ℝ hi lo, p ∉ segment ℝ a b1)
    (hscb : ∀ p ∈ segment ℝ hi lo, p ∉ segment ℝ b2 c)
    (hcol : ∀ p ∈ segment ℝ hi lo, p.2 = b1.2 → 0 < (b1.1 - p.1) * (b2.1 - p.1))
    (hhib : b1.2 ≤ hi.2) (hlob : lo.2 < b1.2) :
    edgeWind a b1 hi + edgeWind b2 c hi = edgeWind a b1 lo + edgeWind b2 c lo := by
  have hqmem : hi ∈ segment ℝ hi lo := left_mem_segment ℝ hi lo
  have hq'mem : lo ∈ segment ℝ hi lo := right_mem_segment ℝ hi lo
  obtain ⟨hale, halt, hale', _⟩ := height_cmp_const_of_segment_off a.2 hoa
  obtain ⟨hcle, hclt, hcle', _⟩ := height_cmp_const_of_segment_off c.2 hoc
  have hsab_s := sign_const_of_segment_off (g := fun p : ℝ × ℝ => cross (b1 - a) (p - a))
    (by simp only [cross]; fun_prop) (q := hi) (q' := lo) hcab
  have hscb_s := sign_const_of_segment_off (g := fun p : ℝ × ℝ => cross (c - b2) (p - b2))
    (by simp only [cross]; fun_prop) (q := hi) (q' := lo) hccb
  set Cab := cross (b1 - a) (hi - a) with hCab
  set Cab' := cross (b1 - a) (lo - a) with hCab'
  set Ccb := cross (c - b2) (hi - b2) with hCcb
  set Ccb' := cross (c - b2) (lo - b2) with hCcb'
  have hCab0 : Cab ≠ 0 := hcab hi hqmem
  have hCab'0 : Cab' ≠ 0 := hcab lo hq'mem
  have hCcb0 : Ccb ≠ 0 := hccb hi hqmem
  have hCcb'0 : Ccb' ≠ 0 := hccb lo hq'mem
  have hPab : (0 < Cab) ↔ (0 < Cab') := hsab_s.1
  have hNab : (Cab < 0) ↔ (Cab' < 0) := hsab_s.2
  have hPcb : (0 < Ccb) ↔ (0 < Ccb') := hscb_s.1
  have hNcb : (Ccb < 0) ↔ (Ccb' < 0) := hscb_s.2
  have hcross_ab : ∀ p : ℝ × ℝ, p.2 = b1.2 →
      cross (b1 - a) (p - a) = (b1.2 - a.2) * (b1.1 - p.1) := by
    intro p hp; simp only [cross, Prod.fst_sub, Prod.snd_sub]; rw [hp]; ring
  have hcross_cb : ∀ p : ℝ × ℝ, p.2 = b2.2 →
      cross (c - b2) (p - b2) = (c.2 - b2.2) * (b2.1 - p.1) := by
    intro p hp; simp only [cross, Prod.fst_sub, Prod.snd_sub]; rw [hp]; ring
  -- extract a crossing point `p` at height `b1.2`
  obtain ⟨p, hpseg', hp2⟩ := segment_attains_height (q := lo) (q' := hi) (h := b1.2)
    (le_of_lt hlob) hhib
  rw [segment_symm] at hpseg'
  have hp2' : p.2 = b2.2 := by rw [hp2, hb]
  -- the two deltas have the same sign
  have hcolp := hcol p hpseg' hp2
  set δ1 := b1.1 - p.1 with hδ1
  set δ2 := b2.1 - p.1 with hδ2
  have hδ12 : 0 < δ1 * δ2 := hcolp
  -- sign of Cab equals sign of (b1.2 - a.2)*δ1, similarly Ccb
  have getDelta : ((Cab < 0) ↔ (b1.2 - a.2) * δ1 < 0) ∧ ((0 < Cab) ↔ (0 < (b1.2 - a.2) * δ1)) ∧
      ((Ccb < 0) ↔ (c.2 - b2.2) * δ2 < 0) ∧ ((0 < Ccb) ↔ (0 < (c.2 - b2.2) * δ2)) := by
    have hsub : segment ℝ hi p ⊆ segment ℝ hi lo :=
      (convex_segment hi lo).segment_subset hqmem hpseg'
    have hsgn := sign_const_of_segment_off
      (g := fun r : ℝ × ℝ => cross (b1 - a) (r - a)) (by simp only [cross]; fun_prop)
      (q := hi) (q' := p) (fun r hr => hcab r (hsub hr))
    have hsgn' := sign_const_of_segment_off
      (g := fun r : ℝ × ℝ => cross (c - b2) (r - b2)) (by simp only [cross]; fun_prop)
      (q := hi) (q' := p) (fun r hr => hccb r (hsub hr))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsgn.2, hcross_ab p hp2]
    · rw [hsgn.1, hcross_ab p hp2]
    · rw [hsgn'.2, hcross_cb p hp2']
    · rw [hsgn'.1, hcross_cb p hp2']
  obtain ⟨hNabδ, hPabδ, hNcbδ, hPcbδ⟩ := getDelta
  have hAlt : (hi.2 < a.2) ↔ (b1.2 - a.2 < 0) := by
    constructor
    · intro h; linarith
    · intro h; by_contra hcon; push_neg at hcon
      exact absurd (hale.mp hcon) (by linarith)
  have hClt : (hi.2 < c.2) ↔ (0 < c.2 - b2.2) := by
    constructor
    · intro h; rw [← hb]; linarith
    · intro h; by_contra hcon; push_neg at hcon
      have : b2.2 ≤ hi.2 := by rw [← hb]; exact hhib
      exact absurd (hcle.mp hcon) (by linarith)
  have e1 : edgeWind a b1 hi = (if hi.2 < a.2 ∧ Cab < 0 then (-1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCab]
    rw [if_neg (show ¬ (a.2 ≤ hi.2 ∧ hi.2 < b1.2 ∧ 0 < Cab) by rintro ⟨_, h, _⟩; linarith)]
    exact if_congr ⟨fun ⟨_, h₂, h₃⟩ => ⟨h₂, h₃⟩, fun ⟨h₂, h₃⟩ => ⟨hhib, h₂, h₃⟩⟩ rfl rfl
  have e2 : edgeWind b2 c hi = (if hi.2 < c.2 ∧ 0 < Ccb then (1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCcb]
    have hhib2 : b2.2 ≤ hi.2 := by rw [← hb]; exact hhib
    rw [if_congr (show (b2.2 ≤ hi.2 ∧ hi.2 < c.2 ∧ 0 < Ccb) ↔ (hi.2 < c.2 ∧ 0 < Ccb) from
      ⟨fun ⟨_, h₂, h₃⟩ => ⟨h₂, h₃⟩, fun ⟨h₂, h₃⟩ => ⟨hhib2, h₂, h₃⟩⟩) rfl rfl]
    rw [if_neg (show ¬ (c.2 ≤ hi.2 ∧ hi.2 < b2.2 ∧ Ccb < 0) by
      rintro ⟨_, h, _⟩; linarith)]
  have e3 : edgeWind a b1 lo = (if a.2 ≤ lo.2 ∧ 0 < Cab' then (1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCab']
    rw [if_congr (show (a.2 ≤ lo.2 ∧ lo.2 < b1.2 ∧ 0 < Cab') ↔ (a.2 ≤ lo.2 ∧ 0 < Cab') from
      ⟨fun ⟨h₁, _, h₃⟩ => ⟨h₁, h₃⟩, fun ⟨h₁, h₃⟩ => ⟨h₁, hlob, h₃⟩⟩) rfl rfl]
    rw [if_neg (show ¬ (b1.2 ≤ lo.2 ∧ lo.2 < a.2 ∧ Cab' < 0) by rintro ⟨h, _, _⟩; linarith)]
  have e4 : edgeWind b2 c lo = (if c.2 ≤ lo.2 ∧ Ccb' < 0 then (-1 : ℤ) else 0) := by
    unfold edgeWind; rw [← hCcb']
    have hlob2 : lo.2 < b2.2 := by rw [← hb]; exact hlob
    rw [if_neg (show ¬ (b2.2 ≤ lo.2 ∧ lo.2 < c.2 ∧ 0 < Ccb') by rintro ⟨h, _, _⟩; linarith)]
    exact if_congr ⟨fun ⟨h₁, _, h₃⟩ => ⟨h₁, h₃⟩, fun ⟨h₁, h₃⟩ => ⟨h₁, hlob2, h₃⟩⟩ rfl rfl
  rw [e1, e2, e3, e4]
  have hprod_ab : (b1.2 - a.2) * δ1 ≠ 0 := by
    rcases (lt_or_gt_of_ne hCab0) with h | h
    · exact ne_of_lt (hNabδ.mp h)
    · exact ne_of_gt (hPabδ.mp h)
  have hprod_cb : (c.2 - b2.2) * δ2 ≠ 0 := by
    rcases (lt_or_gt_of_ne hCcb0) with h | h
    · exact ne_of_lt (hNcbδ.mp h)
    · exact ne_of_gt (hPcbδ.mp h)
  have hba : b1.2 - a.2 ≠ 0 := by
    intro h; apply hprod_ab; rw [h, zero_mul]
  have hcb : c.2 - b2.2 ≠ 0 := by
    intro h; apply hprod_cb; rw [h, zero_mul]
  have hδ1ne : δ1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hδ12; exact lt_irrefl 0 hδ12
  have hδ2ne : δ2 ≠ 0 := by
    intro h; rw [h, mul_zero] at hδ12; exact lt_irrefl 0 hδ12
  have hq'a : (a.2 ≤ lo.2) ↔ (0 < b1.2 - a.2) := by
    rw [← hale]; constructor
    · intro h; rcases lt_or_gt_of_ne hba with hh | hh
      · exact absurd (hAlt.mpr hh) (by linarith)
      · linarith
    · intro h; by_contra hcon; push_neg at hcon
      exact absurd (hAlt.mp hcon) (by linarith)
  have hq'c : (c.2 ≤ lo.2) ↔ (c.2 - b2.2 < 0) := by
    rw [← hcle]; constructor
    · intro h; rcases lt_or_gt_of_ne hcb with hh | hh
      · linarith
      · exact absurd (hClt.mpr hh) (by linarith)
    · intro h; by_contra hcon; push_neg at hcon
      exact absurd (hClt.mp hcon) (by linarith)
  have hPab' : (0 < Cab') ↔ (0 < (b1.2 - a.2) * δ1) := hPab.symm.trans hPabδ
  have hNcb' : (Ccb' < 0) ↔ ((c.2 - b2.2) * δ2 < 0) := hNcb.symm.trans hNcbδ
  simp only [ite_and, hAlt, hNabδ, hClt, hPcbδ, hq'a, hPab', hq'c, hNcb']
  -- δ2 shares δ1's sign (since `0 < δ1 * δ2`)
  have hδ2pos : 0 < δ1 → 0 < δ2 := fun h => by nlinarith
  have hδ2neg : δ1 < 0 → δ2 < 0 := fun h => by nlinarith
  rcases lt_or_gt_of_ne hba with hsab' | hsab' <;>
    rcases lt_or_gt_of_ne hcb with hscb' | hscb' <;>
    rcases lt_or_gt_of_ne hδ1ne with hsδ1 | hsδ1 <;>
    -- in each of the 8 branches both products have concrete sign; record them
    (first
      | (have hPa : 0 < (b1.2 - a.2) * δ1 := by
            first | exact mul_pos hsab' hsδ1 | exact mul_pos_of_neg_of_neg hsab' hsδ1)
      | (have hPa : (b1.2 - a.2) * δ1 < 0 := by
            first | exact mul_neg_of_pos_of_neg hsab' hsδ1
                  | exact mul_neg_of_neg_of_pos hsab' hsδ1)) <;>
    (first
      | (have hPc : 0 < (c.2 - b2.2) * δ2 := by
            first | exact mul_pos hscb' (hδ2pos hsδ1)
                  | exact mul_pos_of_neg_of_neg hscb' (hδ2neg hsδ1))
      | (have hPc : (c.2 - b2.2) * δ2 < 0 := by
            first | exact mul_neg_of_pos_of_neg hscb' (hδ2neg hsδ1)
                  | exact mul_neg_of_neg_of_pos hscb' (hδ2pos hsδ1))) <;>
    split_ifs <;>
      first
        | rfl
        | (exfalso; linarith [hPa, hPc, hsab', hscb', hsδ1])

set_option maxHeartbeats 1600000 in
/-- **Split-middle run cancellation from chord disjointness (crossing case).** The horizontal-run
analogue of `edgeWind_pair_eq_cross_seg_disjoint`: for an entering edge `a→b1` and a leaving edge
`b2→c` with `b1.2 = b2.2`, both non-horizontal, a query segment `hi—lo` straddling the run height
(`b1.2 ≤ hi.2`, `lo.2 < b1.2`) that avoids the outer heights `a.2`, `c.2`, is disjoint from both
chord segments, and whose crossing points at the run height lie off the run's x-span (`hcol`), keeps
the combined contribution fixed. The unique crossing point `p0` (at the run height) is off both `b1`
and `b2` (chord disjointness), so both cross products are nonzero there; by continuity a small
straddling sub-segment `[u,v]` keeps them nonzero, on which `edgeWind_split_pair_cross` gives the
cancellation, while the two outer pieces avoid the run height and are constant by
`edgeWind_split_pair_eq_of_seg_disjoint_off_mid`. -/
lemma edgeWind_split_pair_eq_cross_seg_disjoint (a b1 b2 c hi lo : ℝ × ℝ)
    (hb : b1.2 = b2.2) (hab : a.2 ≠ b1.2) (hcb : c.2 ≠ b2.2)
    (hoa : ∀ p ∈ segment ℝ hi lo, p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ hi lo, p.2 ≠ c.2)
    (hsab : ∀ p ∈ segment ℝ hi lo, p ∉ segment ℝ a b1)
    (hscb : ∀ p ∈ segment ℝ hi lo, p ∉ segment ℝ b2 c)
    (hcol : ∀ p ∈ segment ℝ hi lo, p.2 = b1.2 → 0 < (b1.1 - p.1) * (b2.1 - p.1))
    (hhib : b1.2 < hi.2) (hlob : lo.2 < b1.2) :
    edgeWind a b1 hi + edgeWind b2 c hi = edgeWind a b1 lo + edgeWind b2 c lo := by
  set γ : ℝ → ℝ × ℝ := fun τ => (1 - τ) • hi + τ • lo with hγ
  have hγcont : Continuous γ := by fun_prop
  have hγ0 : γ 0 = hi := by simp [hγ]
  have hγ1 : γ 1 = lo := by simp [hγ]
  have hγmem : ∀ τ ∈ Set.Icc (0:ℝ) 1, γ τ ∈ segment ℝ hi lo := by
    intro τ hτ; exact ⟨1 - τ, τ, by linarith [hτ.2], hτ.1, by ring, rfl⟩
  have hH : ∀ τ : ℝ, (γ τ).2 = (1 - τ) * hi.2 + τ * lo.2 := by
    intro τ; simp [hγ, Prod.snd_add, Prod.smul_snd]
  set τ0 : ℝ := (hi.2 - b1.2) / (hi.2 - lo.2) with hτ0def
  have hden : 0 < hi.2 - lo.2 := by linarith
  have hτ0mem : τ0 ∈ Set.Ioo (0:ℝ) 1 := by
    constructor
    · apply div_pos (by linarith) hden
    · rw [div_lt_one hden]; linarith
  have hHτ0 : (γ τ0).2 = b1.2 := by
    rw [hH τ0, hτ0def]; field_simp; ring
  set p0 : ℝ × ℝ := γ τ0 with hp0def
  have hp0mem : p0 ∈ segment ℝ hi lo := hγmem τ0 ⟨le_of_lt hτ0mem.1, le_of_lt hτ0mem.2⟩
  have hp0ne1 : p0 ≠ b1 := by
    intro h; exact hsab p0 hp0mem (by rw [h]; exact right_mem_segment ℝ a b1)
  have hp0ne2 : p0 ≠ b2 := by
    intro h; exact hscb p0 hp0mem (by rw [h]; exact left_mem_segment ℝ b2 c)
  have hHτ0' : p0.2 = b2.2 := by rw [hHτ0, hb]
  have hFab0 : cross (b1 - a) (p0 - a) ≠ 0 := cross_ne_zero_of_height_ne a b1 p0 hab hHτ0 hp0ne1
  have hFcb0 : cross (c - b2) (p0 - b2) ≠ 0 := by
    have hraw : cross (b2 - c) (p0 - c) ≠ 0 := cross_ne_zero_of_height_ne c b2 p0 hcb hHτ0' hp0ne2
    intro h; apply hraw
    have : cross (b2 - c) (p0 - c) = - cross (c - b2) (p0 - b2) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [this, h, neg_zero]
  set Fab : ℝ → ℝ := fun τ => cross (b1 - a) (γ τ - a) with hFabdef
  set Fcb : ℝ → ℝ := fun τ => cross (c - b2) (γ τ - b2) with hFcbdef
  have hFabcont : Continuous Fab := by simp only [hFabdef, cross]; fun_prop
  have hFcbcont : Continuous Fcb := by simp only [hFcbdef, cross]; fun_prop
  have hev : ∀ᶠ τ in nhds τ0, Fab τ ≠ 0 ∧ Fcb τ ≠ 0 :=
    ((hFabcont.continuousAt).eventually_ne hFab0).and ((hFcbcont.continuousAt).eventually_ne hFcb0)
  obtain ⟨δ, hδpos, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set r : ℝ := min (δ / 2) (min (τ0 / 2) ((1 - τ0) / 2)) with hrdef
  have hrpos : 0 < r := by
    apply lt_min (by linarith)
    exact lt_min (by linarith [hτ0mem.1]) (by linarith [hτ0mem.2])
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrlo : 0 < τ0 - r := by
    have : r ≤ τ0 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hτ0mem.1]
  have hrhi : τ0 + r < 1 := by
    have : r ≤ (1 - τ0) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [hτ0mem.2]
  set τu : ℝ := τ0 - r with hτudef
  set τv : ℝ := τ0 + r with hτvdef
  set u : ℝ × ℝ := γ τu with hudef
  set v : ℝ × ℝ := γ τv with hvdef
  have hτumem : τu ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hτvmem : τv ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have humem : u ∈ segment ℝ hi lo := hγmem τu hτumem
  have hvmem : v ∈ segment ℝ hi lo := hγmem τv hτvmem
  have hsub : segment ℝ u v ⊆ segment ℝ hi lo :=
    (convex_segment hi lo).segment_subset humem hvmem
  have hHmono : ∀ τ1 τ2 : ℝ, τ1 < τ2 → (γ τ2).2 < (γ τ1).2 := by
    intro τ1 τ2 h12
    rw [hH τ1, hH τ2]; nlinarith [hden, h12]
  -- heights at u, v straddle b1.2
  have huhi : b1.2 ≤ u.2 := by
    rw [hudef]
    have : b1.2 < (γ τu).2 := by have := hHmono τu τ0 (by linarith); rw [hHτ0] at this; exact this
    linarith
  have hvlo : v.2 < b1.2 := by
    rw [hvdef]
    have := hHmono τ0 τv (by linarith); rw [hHτ0] at this; exact this
  have hmemparam2 : ∀ (α β : ℝ), α ≤ β → ∀ p ∈ segment ℝ (γ α) (γ β),
      ∃ τ ∈ Set.Icc α β, p = γ τ := by
    intro α β hαβ p hp
    obtain ⟨s, t, hs, ht, hst, hpt⟩ := hp
    have hs' : s = 1 - t := by linarith
    have hγaff : (1 - t) • γ α + t • γ β = γ ((1 - t) * α + t * β) := by
      simp only [hγ]
      have hx : ((1 - ((1 - t) * α + t * β)) : ℝ) = (1 - t) * (1 - α) + t * (1 - β) := by ring
      rw [hx]; module
    refine ⟨(1 - t) * α + t * β, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [hαβ]
    · nlinarith [hαβ]
    · rw [← hpt, hs', hγaff]
  -- cross products nonzero on [u, v], col condition restricted
  have hballall : ∀ τ ∈ Set.Icc τu τv, Fab τ ≠ 0 ∧ Fcb τ ≠ 0 := by
    intro τ hτ
    apply hball
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hcab_uv : ∀ p ∈ segment ℝ u v, cross (b1 - a) (p - a) ≠ 0 := by
    intro p hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam2 τu τv (by linarith) p (by rw [hudef, hvdef] at hp; exact hp)
    rw [hpτ]; exact (hballall τ hτ).1
  have hccb_uv : ∀ p ∈ segment ℝ u v, cross (c - b2) (p - b2) ≠ 0 := by
    intro p hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam2 τu τv (by linarith) p (by rw [hudef, hvdef] at hp; exact hp)
    rw [hpτ]; exact (hballall τ hτ).2
  have hmid : edgeWind a b1 u + edgeWind b2 c u = edgeWind a b1 v + edgeWind b2 c v :=
    edgeWind_split_pair_cross a b1 b2 c u v hb
      (fun p hp => hoa p (hsub hp)) (fun p hp => hoc p (hsub hp))
      hcab_uv hccb_uv
      (fun p hp => hsab p (hsub hp)) (fun p hp => hscb p (hsub hp))
      (fun p hp => hcol p (hsub hp)) huhi hvlo
  -- outer pieces avoid b1.2 (and b2.2)
  have hob_qu : ∀ p ∈ segment ℝ hi u, p.2 ≠ b1.2 := by
    intro p hp
    rw [← hγ0] at hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam2 0 τu (by linarith) p hp
    rw [hpτ]
    have : b1.2 < (γ τu).2 := by
      have := hHmono τu τ0 (by linarith); rw [hHτ0] at this; exact this
    have hmono2 : (γ τu).2 ≤ (γ τ).2 := by
      rcases eq_or_lt_of_le hτ.2 with h | h
      · rw [h]
      · exact le_of_lt (hHmono τ τu h)
    linarith
  have hob_vq : ∀ p ∈ segment ℝ v lo, p.2 ≠ b1.2 := by
    intro p hp
    rw [← hγ1] at hp
    obtain ⟨τ, hτ, hpτ⟩ := hmemparam2 τv 1 (by linarith) p hp
    rw [hpτ]
    have hlt : (γ τv).2 < b1.2 := by
      have := hHmono τ0 τv (by linarith); rw [hHτ0] at this; exact this
    have hmono2 : (γ τ).2 ≤ (γ τv).2 := by
      rcases eq_or_lt_of_le hτ.1 with h | h
      · rw [← h]
      · exact le_of_lt (hHmono τv τ h)
    linarith
  have hsubqu : segment ℝ hi u ⊆ segment ℝ hi lo :=
    (convex_segment hi lo).segment_subset (left_mem_segment ℝ hi lo) humem
  have hsubvq : segment ℝ v lo ⊆ segment ℝ hi lo :=
    (convex_segment hi lo).segment_subset hvmem (right_mem_segment ℝ hi lo)
  have hleft : edgeWind a b1 hi + edgeWind b2 c hi = edgeWind a b1 u + edgeWind b2 c u :=
    edgeWind_split_pair_eq_of_seg_disjoint_off_mid a b1 b2 c hi u
      (fun p hp => hoa p (hsubqu hp)) hob_qu (by rw [← hb]; exact hob_qu)
      (fun p hp => hoc p (hsubqu hp))
      (fun p hp => hsab p (hsubqu hp)) (fun p hp => hscb p (hsubqu hp))
  have hright : edgeWind a b1 v + edgeWind b2 c v = edgeWind a b1 lo + edgeWind b2 c lo :=
    edgeWind_split_pair_eq_of_seg_disjoint_off_mid a b1 b2 c v lo
      (fun p hp => hoa p (hsubvq hp)) hob_vq (by rw [← hb]; exact hob_vq)
      (fun p hp => hoc p (hsubvq hp))
      (fun p hp => hsab p (hsubvq hp)) (fun p hp => hscb p (hsubvq hp))
  rw [hleft, hmid, hright]

/-- **Pair constancy of `edgeWind` across a horizontal run (the step-1 run-crossing engine).**
For an entering edge `a→b1` and a leaving edge `b2→c` whose middle endpoints share a height
(`b1.2 = b2.2`), a query segment `q—q'` avoiding the outer heights `a.2`, `c.2`, with both endpoints
off the run height `b1.2`, disjoint from both chord segments `[a,b1]`, `[b2,c]`, and whose every
crossing point at height `b1.2` lies off the run's x-span (`hcol`, ensuring the two flips cancel),
keeps the combined contribution unchanged — even when the segment freely **crosses** the run height.
A horizontal entering/leaving edge contributes `0` and the sum reduces to the other edge's individual
constancy; if both endpoints stay on one side of the run height the whole (height-affine) segment
avoids it and each edge is individually constant (`edgeWind_split_pair_eq_of_seg_disjoint_off_mid`);
if they straddle it the run cancellation `edgeWind_split_pair_cross` keeps the sum fixed. This is the
multi-vertex generalisation of `edgeWind_pair_eq_of_seg_disjoint`, collapsing a horizontal run to its
two flanking edges. -/
lemma edgeWind_run_cross (a b1 b2 c q q' : ℝ × ℝ)
    (hb : b1.2 = b2.2)
    (hoa : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2)
    (hoc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2)
    (hqb : q.2 ≠ b1.2) (hq'b : q'.2 ≠ b1.2)
    (hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b1)
    (hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ b2 c)
    (hcol : ∀ p ∈ segment ℝ q q', p.2 = b1.2 → 0 < (b1.1 - p.1) * (b2.1 - p.1)) :
    edgeWind a b1 q + edgeWind b2 c q = edgeWind a b1 q' + edgeWind b2 c q' := by
  by_cases hab : a.2 = b1.2
  · rw [edgeWind_eq_zero_of_eq_height a b1 q hab, edgeWind_eq_zero_of_eq_height a b1 q' hab]
    have hob2 : ∀ p ∈ segment ℝ q q', p.2 ≠ b2.2 := by
      intro p hp hpb; exact hoa p hp (by rw [hab, hb]; exact hpb)
    rw [edgeWind_eq_of_seg_disjoint b2 c q q' hob2 hoc hscb]
  by_cases hcb : c.2 = b2.2
  · rw [edgeWind_eq_zero_of_eq_height b2 c q hcb.symm, edgeWind_eq_zero_of_eq_height b2 c q' hcb.symm]
    have hob1 : ∀ p ∈ segment ℝ q q', p.2 ≠ b1.2 := by
      rw [hb]; intro p hp hpb; exact hoc p hp (by rw [hcb]; exact hpb)
    rw [edgeWind_eq_of_seg_disjoint a b1 q q' hoa hob1 hsab]
  -- both edges non-horizontal: split on the side of the run height b1.2
  have hcb' : c.2 ≠ b2.2 := hcb
  rcases lt_or_gt_of_ne hqb with hqlt | hqgt <;> rcases lt_or_gt_of_ne hq'b with hq'lt | hq'gt
  · -- both below b1.2: whole segment avoids b1.2 and b2.2
    have hob1 : ∀ p ∈ segment ℝ q q', p.2 ≠ b1.2 := by
      intro p hp
      obtain ⟨s, t, hs, ht, hst, hpt⟩ := hp
      have hh : p.2 = s * q.2 + t * q'.2 := by rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
      intro hpb
      rw [hpb] at hh
      have hsum : s * b1.2 + t * b1.2 = b1.2 := by rw [← add_mul, hst, one_mul]
      have h1 : s * q.2 ≤ s * b1.2 := mul_le_mul_of_nonneg_left hqlt.le hs
      have h2 : t * q'.2 ≤ t * b1.2 := mul_le_mul_of_nonneg_left hq'lt.le ht
      rcases lt_or_eq_of_le hs with hsp | hs0
      · have h3 : s * q.2 < s * b1.2 := mul_lt_mul_of_pos_left hqlt hsp
        linarith [h1, h2, h3, hsum, hh]
      · have ht1 : t = 1 := by linarith
        have h3 : t * q'.2 < t * b1.2 := by rw [ht1]; simpa using hq'lt
        linarith [h1, h2, h3, hsum, hh]
    exact edgeWind_split_pair_eq_of_seg_disjoint_off_mid a b1 b2 c q q' hoa hob1
      (by rw [← hb]; exact hob1) hoc hsab hscb
  · -- q below, q' above: straddle (reverse orientation)
    exact (edgeWind_split_pair_eq_cross_seg_disjoint a b1 b2 c q' q hb hab hcb'
      (fun p hp => hoa p (by rwa [segment_symm] at hp))
      (fun p hp => hoc p (by rwa [segment_symm] at hp))
      (fun p hp => hsab p (by rwa [segment_symm] at hp))
      (fun p hp => hscb p (by rwa [segment_symm] at hp))
      (fun p hp => hcol p (by rwa [segment_symm] at hp))
      hq'gt hqlt).symm
  · -- q above, q' below: straddle (direct orientation)
    exact edgeWind_split_pair_eq_cross_seg_disjoint a b1 b2 c q q' hb hab hcb'
      hoa hoc hsab hscb hcol hqgt hq'lt
  · -- both above b1.2: whole segment avoids b1.2 and b2.2
    have hob1 : ∀ p ∈ segment ℝ q q', p.2 ≠ b1.2 := by
      intro p hp
      obtain ⟨s, t, hs, ht, hst, hpt⟩ := hp
      have hh : p.2 = s * q.2 + t * q'.2 := by rw [← hpt]; simp [Prod.snd_add, Prod.smul_snd]
      intro hpb
      rw [hpb] at hh
      have hsum : s * b1.2 + t * b1.2 = b1.2 := by rw [← add_mul, hst, one_mul]
      have h1 : s * b1.2 ≤ s * q.2 := mul_le_mul_of_nonneg_left hqgt.le hs
      have h2 : t * b1.2 ≤ t * q'.2 := mul_le_mul_of_nonneg_left hq'gt.le ht
      rcases lt_or_eq_of_le hs with hsp | hs0
      · have h3 : s * b1.2 < s * q.2 := mul_lt_mul_of_pos_left hqgt hsp
        linarith [h1, h2, h3, hsum, hh]
      · have ht1 : t = 1 := by linarith
        have h3 : t * b1.2 < t * q'.2 := by rw [ht1]; simpa using hq'gt
        linarith [h1, h2, h3, hsum, hh]
    exact edgeWind_split_pair_eq_of_seg_disjoint_off_mid a b1 b2 c q q' hoa hob1
      (by rw [← hb]; exact hob1) hoc hsab hscb

/-- **Height-collapse normalisation.** Removes the head `a` of any consecutive pair `a :: b :: …`
that shares a height (`a.2 = b.2`), iterating from the front. The result has no two consecutive
vertices at a common height. -/
noncomputable def collapseEq : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | [a] => [a]
  | a :: b :: rest => if a.2 = b.2 then collapseEq (b :: rest) else a :: collapseEq (b :: rest)

lemma collapseEq_nil : collapseEq [] = [] := rfl
lemma collapseEq_singleton (a : ℝ × ℝ) : collapseEq [a] = [a] := rfl
lemma collapseEq_cons₂ (a b : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    collapseEq (a :: b :: rest) =
      if a.2 = b.2 then collapseEq (b :: rest) else a :: collapseEq (b :: rest) := rfl

lemma collapseEq_head_height (a : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    ∃ c, (collapseEq (a :: rest)).head? = some c ∧ c.2 = a.2 := by
  induction rest generalizing a with
  | nil => exact ⟨a, rfl, rfl⟩
  | cons b rest ih =>
    rw [collapseEq_cons₂]
    by_cases hab : a.2 = b.2
    · rw [if_pos hab]
      obtain ⟨c, hc, hc2⟩ := ih b
      exact ⟨c, hc, by rw [hc2, hab]⟩
    · rw [if_neg hab]; exact ⟨a, rfl, rfl⟩

/-- **`collapseEq` produces a polyline with no adjacent equal-height pair, at every height.**
After collapsing, no two consecutive vertices share a height; in particular `noAdjAtHeight h` holds
for every `h`. -/
lemma noAdjAtHeight_collapseEq (h : ℝ) :
    ∀ pts : List (ℝ × ℝ), noAdjAtHeight h (collapseEq pts) := by
  intro pts
  induction pts using collapseEq.induct with
  | case1 => exact True.intro
  | case2 a => exact True.intro
  | case3 a b rest hab ih =>
    rw [collapseEq_cons₂, if_pos hab]; exact ih
  | case4 a b rest hab ih =>
    rw [collapseEq_cons₂, if_neg hab]
    obtain ⟨c, hc, hc2⟩ := collapseEq_head_height b rest
    -- collapseEq (b :: rest) = c :: tail
    cases hcl : collapseEq (b :: rest) with
    | nil => rw [hcl] at hc; simp at hc
    | cons c' tail =>
      rw [hcl] at hc; simp only [List.head?_cons, Option.some.injEq] at hc
      subst hc
      rw [noAdjAtHeight_cons₂]
      refine ⟨?_, ?_⟩
      · rintro ⟨ha, hc'⟩
        exact hab (by rw [ha, ← hc2, hc'])
      · rw [← hcl]; exact ih

lemma chainWind_cross_one_height_free_aux (h : ℝ) (q q' : ℝ × ℝ)
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h) :
    ∀ (n : ℕ) (pts : List (ℝ × ℝ)), pts.length ≤ n →
      chainChordDisjoint q q' pts →
      (∀ v ∈ pts, (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h) →
      (∀ a ∈ pts.head?, a.2 ≠ h) →
      (∀ a ∈ pts.getLast?, a.2 ≠ h) →
      (∀ p ∈ segment ℝ q q', p.2 = h → ∀ v ∈ pts, v.2 = h → ∀ w ∈ pts, w.2 = h →
        0 < (v.1 - p.1) * (w.1 - p.1)) →
      chainWind pts q = chainWind pts q' := by
  have hrc : ∀ (cc : ℝ × ℝ) (rr : List (ℝ × ℝ)) (r : ℝ × ℝ) (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)),
      (∀ v ∈ b₀ :: rn, v.2 = h) →
      chainWind (b₀ :: rn ++ cc :: rr) r
        = LatticePolygon.edgeWind ((b₀ :: rn).getLast (by simp)) cc r + chainWind (cc :: rr) r := by
    intro cc rr r b₀ rn
    induction rn generalizing b₀ with
    | nil => intro _; simp [chainWind_cons₂]
    | cons b' rn' ih =>
      intro hall
      rw [List.cons_append, List.cons_append, chainWind_cons₂,
        edgeWind_eq_zero_of_eq_height b₀ b' r (by rw [hall b₀ (by simp), hall b' (by simp)]), zero_add]
      rw [← List.cons_append, ih b' (fun v hv => hall v (by simp at hv ⊢; tauto))]
      congr 2
  have hccd : ∀ (cc : ℝ × ℝ) (rr : List (ℝ × ℝ)) (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)),
      chainChordDisjoint q q' (b₀ :: rn ++ cc :: rr) →
      (∀ p ∈ segment ℝ q q', p ∉ segment ℝ ((b₀ :: rn).getLast (by simp)) cc) := by
    intro cc rr b₀ rn
    induction rn generalizing b₀ with
    | nil =>
      intro hcd
      have hcd' := (chainChordDisjoint_cons₂ q q' b₀ cc rr).mp hcd
      simpa using hcd'.1
    | cons b' rn' ih =>
      intro hcd
      have hcd' := (chainChordDisjoint_cons₂ q q' b₀ b' (rn' ++ cc :: rr)).mp hcd
      have := ih b' hcd'.2
      simpa using this
  have hdrop : ∀ (cc : ℝ × ℝ) (rr pre : List (ℝ × ℝ)),
      chainChordDisjoint q q' (pre ++ cc :: rr) → chainChordDisjoint q q' (cc :: rr) := by
    intro cc rr pre
    induction pre with
    | nil => intro hcd; simpa using hcd
    | cons x xs ihp =>
      intro hcd
      exact ihp (chainChordDisjoint_tail q q' x (xs ++ cc :: rr) (by simpa using hcd))
  intro n
  induction n with
  | zero =>
    intro pts hlen _ _ _ _ _
    rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen; rfl
  | succ n ih =>
    intro pts hlen hchord hheights hhead hlast hcol
    match pts with
    | [] => rfl
    | [a] => rfl
    | a :: b :: rest =>
      have hah : a.2 ≠ h := hhead a (by simp)
      rw [chainChordDisjoint_cons₂] at hchord
      by_cases hbh : b.2 = h
      · obtain ⟨run', c, rest'', hsplit, hbrun, hch⟩ : ∃ (run' : List (ℝ × ℝ)) (c : ℝ × ℝ)
            (rest'' : List (ℝ × ℝ)),
            rest = run' ++ c :: rest'' ∧ (∀ v ∈ b :: run', v.2 = h) ∧ c.2 ≠ h := by
          classical
          set run' := rest.takeWhile (fun v => decide (v.2 = h)) with hrun'
          set tail := rest.dropWhile (fun v => decide (v.2 = h)) with htail
          have hsplit : run' ++ tail = rest := List.takeWhile_append_dropWhile
          have hrunh : ∀ v ∈ run', v.2 = h := by
            intro v hv; have := List.mem_takeWhile_imp hv; simpa using this
          have hbrun : ∀ v ∈ b :: run', v.2 = h := by
            intro v hv; rcases List.mem_cons.mp hv with rfl | hv
            · exact hbh
            · exact hrunh v hv
          cases htl : tail with
          | nil =>
            exfalso
            rw [htl, List.append_nil] at hsplit
            have hall : ∀ v ∈ b :: rest, v.2 = h := by rw [← hsplit]; exact hbrun
            obtain ⟨z, hz⟩ := List.getLast?_isSome.mpr (by simp : (b :: rest) ≠ []) |>
              Option.isSome_iff_exists.mp
            exact hlast z (by rw [List.getLast?_cons_cons]; exact hz) (hall z (List.mem_of_getLast? hz))
          | cons c rest'' =>
            refine ⟨run', c, rest'', ?_, hbrun, ?_⟩
            · rw [← hsplit, htl]
            · have hc := List.head_dropWhile_not (fun v => decide (v.2 = h)) (l := rest)
              rw [← htail, htl] at hc
              simpa using hc (by simp)
        subst hsplit
        set bk := (b :: run').getLast (by simp) with hbkdef
        have hbkmem : bk ∈ b :: run' := by rw [hbkdef]; exact List.getLast_mem _
        have hbkh : bk.2 = h := hbrun bk hbkmem
        have hchordtail : chainChordDisjoint q q' (c :: rest'') :=
          hdrop c rest'' (b :: run') hchord.2
        -- recurse on c :: rest''
        have hrec : chainWind (c :: rest'') q = chainWind (c :: rest'') q' := by
          apply ih (c :: rest'') (by simp only [List.length_cons, List.length_append] at hlen ⊢; omega)
            hchordtail
          · intro v hv; exact hheights v (by simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto)
          · intro x hx; simp only [List.head?_cons, Option.mem_some_iff] at hx; rw [← hx]; exact hch
          · intro x hx
            apply hlast x
            have he : (a :: b :: (run' ++ c :: rest'')).getLast? = (c :: rest'').getLast? := by
              have hassoc : a :: b :: (run' ++ c :: rest'') = (a :: b :: run') ++ (c :: rest'') := by simp
              rw [hassoc, List.getLast?_append_cons]
            rw [he]; exact hx
          · intro p hp hpval v hv hvh w hw hwh
            exact hcol p hp hpval v (by simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto)
              hvh w (by simp only [List.mem_cons, List.mem_append] at hw ⊢; tauto) hwh
        -- assemble run step
        have hac : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2 := by
          rcases hheights a (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hah
        have hcc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2 := by
          rcases hheights c (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hch
        have hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b := hchord.1
        have hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ bk c := by
          rw [hbkdef]; exact hccd c rest'' b run' hchord.2
        have hcolbk : ∀ p ∈ segment ℝ q q', p.2 = h → 0 < (b.1 - p.1) * (bk.1 - p.1) := by
          intro p hp hpval
          have hbmem : b ∈ a :: b :: (run' ++ c :: rest'') := by simp
          have hbkmem' : bk ∈ a :: b :: (run' ++ c :: rest'') := by
            have hm : bk ∈ b :: run' := hbkmem
            simp only [List.mem_cons] at hm ⊢
            rcases hm with h1 | h1
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr (List.mem_append_left _ h1))
          exact hcol p hp hpval b hbmem (hbrun b (by simp)) bk hbkmem' hbkh
        have hcw : ∀ r : ℝ × ℝ, chainWind (a :: b :: (run' ++ c :: rest'')) r
            = LatticePolygon.edgeWind a b r + (LatticePolygon.edgeWind bk c r + chainWind (c :: rest'') r) := by
          intro r
          rw [chainWind_cons₂]
          rw [show b :: (run' ++ c :: rest'') = b :: run' ++ c :: rest'' from rfl,
            hrc c rest'' r b run' hbrun, ← hbkdef]
        rw [hcw q, hcw q']
        have hwind := edgeWind_run_cross a b bk c q q' (by rw [hbkh, hbrun b (by simp)]) hac hcc
          (by rw [hbrun b (by simp)]; exact hqh) (by rw [hbrun b (by simp)]; exact hq'h) hsab hscb
          (by intro p hp hpb; rw [hbrun b (by simp)] at hpb; exact hcolbk p hp hpb)
        rw [hrec] at *
        linarith [hwind]
      · -- b off h: edge a→b individually constant; recurse on b::rest
        have hab : ∀ p ∈ segment ℝ q q', p.2 ≠ b.2 := by
          rcases hheights b (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hbh
        have hac : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2 := by
          rcases hheights a (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hah
        have hedge := edgeWind_eq_of_seg_disjoint a b q q' hac hab hchord.1
        have hrec : chainWind (b :: rest) q = chainWind (b :: rest) q' := by
          apply ih (b :: rest) (by simp at hlen ⊢; omega) hchord.2
          · intro v hv; exact hheights v (by simp [hv])
          · intro x hx; simp only [List.head?_cons, Option.mem_some_iff] at hx; rw [← hx]; exact hbh
          · intro x hx
            apply hlast x
            rw [List.getLast?_cons_cons]
            exact hx
          · intro p hp hpval v hv hvh w hw hwh
            exact hcol p hp hpval v (by simp [hv]) hvh w (by simp [hw]) hwh
        rw [chainWind_cons₂, chainWind_cons₂, hedge, hrec]

/-- **`chainWind` transport across exactly one shared vertex-height value `h`, run-aware
(`noAdjAtHeight`-free).** Public form of `chainWind_cross_one_height_free_aux`: along a query
segment `q—q'` disjoint from every chord (`chainChordDisjoint`), with each vertex either at height
`h` or having its height avoided by the whole segment, both list endpoints off `h`, the endpoints
`q`, `q'` off `h`, and — in place of `noAdjAtHeight` — the *column* hypothesis `hcol` saying that at
any crossing point `p` (height `h`) of the segment, every pair of height-`h` vertices lies on the
same side of `p` (so a maximal height-`h` run collapses to its two flanking edges via
`edgeWind_run_cross`), the open-polyline winding is unchanged. -/
lemma chainWind_cross_one_height_free (h : ℝ) (q q' : ℝ × ℝ) (pts : List (ℝ × ℝ))
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h)
    (hchord : chainChordDisjoint q q' pts)
    (hheights : ∀ v ∈ pts, (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h)
    (hhead : ∀ a ∈ pts.head?, a.2 ≠ h)
    (hlast : ∀ a ∈ pts.getLast?, a.2 ≠ h)
    (hcol : ∀ p ∈ segment ℝ q q', p.2 = h → ∀ v ∈ pts, v.2 = h → ∀ w ∈ pts, w.2 = h →
      0 < (v.1 - p.1) * (w.1 - p.1)) :
    chainWind pts q = chainWind pts q' :=
  chainWind_cross_one_height_free_aux h q q' hqh hq'h pts.length pts le_rfl hchord hheights hhead
    hlast hcol

/-- **Off a horizontal chord ⇒ same x-side of both endpoints.** If `b`, `bk` and `p` all lie at
one common height (`b.2 = bk.2`, `p.2 = b.2`) and `p` is *not* on the (horizontal) segment from `b`
to `bk`, then `p`'s x-coordinate is strictly outside the interval `[b.1, bk.1]`, i.e.
`0 < (b.1 - p.1) * (bk.1 - p.1)`. This is the bridge that turns the per-run *segment disjointness*
of a query from a height-`h` run's horizontal hull into the *column* hypothesis consumed by
`edgeWind_run_cross`. -/
lemma prod_pos_of_not_mem_horizontal_segment (b bk p : ℝ × ℝ)
    (hbk : b.2 = bk.2) (hpb : p.2 = b.2) (hpnot : p ∉ segment ℝ b bk) :
    0 < (b.1 - p.1) * (bk.1 - p.1) := by
  rcases lt_trichotomy ((b.1 - p.1) * (bk.1 - p.1)) 0 with hneg | hzero | hpos
  · exfalso; apply hpnot
    have hbkb : bk.1 - b.1 ≠ 0 := by
      intro he
      have : bk.1 = b.1 := by linarith
      rw [this] at hneg; nlinarith [hneg, sq_nonneg (b.1 - p.1)]
    set t := (p.1 - b.1) / (bk.1 - b.1) with ht
    have hpt1 : (1 - t) * b.1 + t * bk.1 = p.1 := by
      rw [ht]; field_simp; ring
    have htge : 0 ≤ t := by
      rw [ht]
      rcases lt_or_gt_of_ne hbkb with hlt | hgt
      · rw [div_nonneg_iff]; right; constructor <;> nlinarith [hneg]
      · rw [div_nonneg_iff]; left; constructor <;> nlinarith [hneg]
    have htle : t ≤ 1 := by
      rw [ht]
      rcases lt_or_gt_of_ne hbkb with hlt | hgt
      · rw [div_le_one_of_neg hlt]; nlinarith [hneg]
      · rw [div_le_one hgt]; nlinarith [hneg]
    refine ⟨1 - t, t, by linarith, htge, by ring, ?_⟩
    have hpt2 : (1 - t) * b.2 + t * bk.2 = p.2 := by rw [← hbk, hpb]; ring
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; rw [hpt1]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [hpt2]
  · exfalso; apply hpnot
    rcases mul_eq_zero.mp hzero with h0 | h0
    · have : p = b := Prod.ext (by linarith [h0]) hpb
      rw [this]; exact left_mem_segment _ _ _
    · have : p = bk := Prod.ext (by linarith [h0]) (by rw [hpb, hbk])
      rw [this]; exact right_mem_segment _ _ _
  · exact hpos

/-- **Per-run version of `chainWind_cross_one_height_free_aux`.** Same conclusion, but the global
all-pairs column hypothesis `hcol` is replaced by the strictly weaker, dischargeable *per-run*
hypothesis `hrun`: for every maximal-or-shorter contiguous height-`h` block `b₀ :: rn` occurring as
an infix of `pts`, the query segment `q—q'` is disjoint from that block's horizontal hull
`segment b₀ (b₀::rn).getLast`. (The hull is a union of horizontal arc edges ⊆ arc, which a query
just off the arc misses.) The column condition consumed by `edgeWind_run_cross` is recovered run by
run via `prod_pos_of_not_mem_horizontal_segment`. -/
lemma chainWind_cross_one_height_free_aux' (h : ℝ) (q q' : ℝ × ℝ)
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h) :
    ∀ (n : ℕ) (pts : List (ℝ × ℝ)), pts.length ≤ n →
      chainChordDisjoint q q' pts →
      (∀ v ∈ pts, (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h) →
      (∀ a ∈ pts.head?, a.2 ≠ h) →
      (∀ a ∈ pts.getLast?, a.2 ≠ h) →
      (∀ (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)), b₀ :: rn <:+: pts → (∀ v ∈ b₀ :: rn, v.2 = h) →
        Disjoint (segment ℝ q q') (segment ℝ b₀ ((b₀ :: rn).getLast (by simp)))) →
      chainWind pts q = chainWind pts q' := by
  have hrc : ∀ (cc : ℝ × ℝ) (rr : List (ℝ × ℝ)) (r : ℝ × ℝ) (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)),
      (∀ v ∈ b₀ :: rn, v.2 = h) →
      chainWind (b₀ :: rn ++ cc :: rr) r
        = LatticePolygon.edgeWind ((b₀ :: rn).getLast (by simp)) cc r + chainWind (cc :: rr) r := by
    intro cc rr r b₀ rn
    induction rn generalizing b₀ with
    | nil => intro _; simp [chainWind_cons₂]
    | cons b' rn' ih =>
      intro hall
      rw [List.cons_append, List.cons_append, chainWind_cons₂,
        edgeWind_eq_zero_of_eq_height b₀ b' r (by rw [hall b₀ (by simp), hall b' (by simp)]), zero_add]
      rw [← List.cons_append, ih b' (fun v hv => hall v (by simp at hv ⊢; tauto))]
      congr 2
  have hccd : ∀ (cc : ℝ × ℝ) (rr : List (ℝ × ℝ)) (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)),
      chainChordDisjoint q q' (b₀ :: rn ++ cc :: rr) →
      (∀ p ∈ segment ℝ q q', p ∉ segment ℝ ((b₀ :: rn).getLast (by simp)) cc) := by
    intro cc rr b₀ rn
    induction rn generalizing b₀ with
    | nil =>
      intro hcd
      have hcd' := (chainChordDisjoint_cons₂ q q' b₀ cc rr).mp hcd
      simpa using hcd'.1
    | cons b' rn' ih =>
      intro hcd
      have hcd' := (chainChordDisjoint_cons₂ q q' b₀ b' (rn' ++ cc :: rr)).mp hcd
      have := ih b' hcd'.2
      simpa using this
  have hdrop : ∀ (cc : ℝ × ℝ) (rr pre : List (ℝ × ℝ)),
      chainChordDisjoint q q' (pre ++ cc :: rr) → chainChordDisjoint q q' (cc :: rr) := by
    intro cc rr pre
    induction pre with
    | nil => intro hcd; simpa using hcd
    | cons x xs ihp =>
      intro hcd
      exact ihp (chainChordDisjoint_tail q q' x (xs ++ cc :: rr) (by simpa using hcd))
  intro n
  induction n with
  | zero =>
    intro pts hlen _ _ _ _ _
    rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen; rfl
  | succ n ih =>
    intro pts hlen hchord hheights hhead hlast hrun
    match pts with
    | [] => rfl
    | [a] => rfl
    | a :: b :: rest =>
      have hah : a.2 ≠ h := hhead a (by simp)
      rw [chainChordDisjoint_cons₂] at hchord
      by_cases hbh : b.2 = h
      · obtain ⟨run', c, rest'', hsplit, hbrun, hch⟩ : ∃ (run' : List (ℝ × ℝ)) (c : ℝ × ℝ)
            (rest'' : List (ℝ × ℝ)),
            rest = run' ++ c :: rest'' ∧ (∀ v ∈ b :: run', v.2 = h) ∧ c.2 ≠ h := by
          classical
          set run' := rest.takeWhile (fun v => decide (v.2 = h)) with hrun'
          set tail := rest.dropWhile (fun v => decide (v.2 = h)) with htail
          have hsplit : run' ++ tail = rest := List.takeWhile_append_dropWhile
          have hrunh : ∀ v ∈ run', v.2 = h := by
            intro v hv; have := List.mem_takeWhile_imp hv; simpa using this
          have hbrun : ∀ v ∈ b :: run', v.2 = h := by
            intro v hv; rcases List.mem_cons.mp hv with rfl | hv
            · exact hbh
            · exact hrunh v hv
          cases htl : tail with
          | nil =>
            exfalso
            rw [htl, List.append_nil] at hsplit
            have hall : ∀ v ∈ b :: rest, v.2 = h := by rw [← hsplit]; exact hbrun
            obtain ⟨z, hz⟩ := List.getLast?_isSome.mpr (by simp : (b :: rest) ≠ []) |>
              Option.isSome_iff_exists.mp
            exact hlast z (by rw [List.getLast?_cons_cons]; exact hz) (hall z (List.mem_of_getLast? hz))
          | cons c rest'' =>
            refine ⟨run', c, rest'', ?_, hbrun, ?_⟩
            · rw [← hsplit, htl]
            · have hc := List.head_dropWhile_not (fun v => decide (v.2 = h)) (l := rest)
              rw [← htail, htl] at hc
              simpa using hc (by simp)
        subst hsplit
        set bk := (b :: run').getLast (by simp) with hbkdef
        have hbkmem : bk ∈ b :: run' := by rw [hbkdef]; exact List.getLast_mem _
        have hbkh : bk.2 = h := hbrun bk hbkmem
        have hchordtail : chainChordDisjoint q q' (c :: rest'') :=
          hdrop c rest'' (b :: run') hchord.2
        have hrun_tail : ∀ (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)), b₀ :: rn <:+: c :: rest'' →
            (∀ v ∈ b₀ :: rn, v.2 = h) →
            Disjoint (segment ℝ q q') (segment ℝ b₀ ((b₀ :: rn).getLast (by simp))) := by
          intro b₀ rn hinf hall
          refine hrun b₀ rn ?_ hall
          refine hinf.trans (List.IsSuffix.isInfix ?_)
          exact (List.suffix_append run' (c :: rest'')).trans (by simp [List.suffix_cons_iff])
        -- recurse on c :: rest''
        have hrec : chainWind (c :: rest'') q = chainWind (c :: rest'') q' := by
          apply ih (c :: rest'') (by simp only [List.length_cons, List.length_append] at hlen ⊢; omega)
            hchordtail
          · intro v hv; exact hheights v (by simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto)
          · intro x hx; simp only [List.head?_cons, Option.mem_some_iff] at hx; rw [← hx]; exact hch
          · intro x hx
            apply hlast x
            have he : (a :: b :: (run' ++ c :: rest'')).getLast? = (c :: rest'').getLast? := by
              have hassoc : a :: b :: (run' ++ c :: rest'') = (a :: b :: run') ++ (c :: rest'') := by simp
              rw [hassoc, List.getLast?_append_cons]
            rw [he]; exact hx
          · exact hrun_tail
        -- assemble run step
        have hac : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2 := by
          rcases hheights a (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hah
        have hcc : ∀ p ∈ segment ℝ q q', p.2 ≠ c.2 := by
          rcases hheights c (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hch
        have hsab : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b := hchord.1
        have hscb : ∀ p ∈ segment ℝ q q', p ∉ segment ℝ bk c := by
          rw [hbkdef]; exact hccd c rest'' b run' hchord.2
        -- per-run disjointness for this run's hull, from hrun
        have hinf_run : b :: run' <:+: a :: b :: (run' ++ c :: rest'') := by
          refine ⟨[a], c :: rest'', ?_⟩; simp
        have hdisj : Disjoint (segment ℝ q q') (segment ℝ b bk) := by
          have := hrun b run' hinf_run hbrun
          rwa [← hbkdef] at this
        have hcolbk : ∀ p ∈ segment ℝ q q', p.2 = h → 0 < (b.1 - p.1) * (bk.1 - p.1) := by
          intro p hp hpval
          have hpnot : p ∉ segment ℝ b bk := fun hpm => Set.disjoint_left.mp hdisj hp hpm
          exact prod_pos_of_not_mem_horizontal_segment b bk p
            (by rw [hbrun b (by simp), hbkh]) (by rw [hpval, hbrun b (by simp)]) hpnot
        have hcw : ∀ r : ℝ × ℝ, chainWind (a :: b :: (run' ++ c :: rest'')) r
            = LatticePolygon.edgeWind a b r + (LatticePolygon.edgeWind bk c r + chainWind (c :: rest'') r) := by
          intro r
          rw [chainWind_cons₂]
          rw [show b :: (run' ++ c :: rest'') = b :: run' ++ c :: rest'' from rfl,
            hrc c rest'' r b run' hbrun, ← hbkdef]
        rw [hcw q, hcw q']
        have hwind := edgeWind_run_cross a b bk c q q' (by rw [hbkh, hbrun b (by simp)]) hac hcc
          (by rw [hbrun b (by simp)]; exact hqh) (by rw [hbrun b (by simp)]; exact hq'h) hsab hscb
          (by intro p hp hpb; rw [hbrun b (by simp)] at hpb; exact hcolbk p hp hpb)
        rw [hrec] at *
        linarith [hwind]
      · -- b off h: edge a→b individually constant; recurse on b::rest
        have hab : ∀ p ∈ segment ℝ q q', p.2 ≠ b.2 := by
          rcases hheights b (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hbh
        have hac : ∀ p ∈ segment ℝ q q', p.2 ≠ a.2 := by
          rcases hheights a (by simp) with hcase | hcase
          · exact hcase
          · exact absurd hcase hah
        have hedge := edgeWind_eq_of_seg_disjoint a b q q' hac hab hchord.1
        have hrec : chainWind (b :: rest) q = chainWind (b :: rest) q' := by
          apply ih (b :: rest) (by simp at hlen ⊢; omega) hchord.2
          · intro v hv; exact hheights v (by simp [hv])
          · intro x hx; simp only [List.head?_cons, Option.mem_some_iff] at hx; rw [← hx]; exact hbh
          · intro x hx
            apply hlast x
            rw [List.getLast?_cons_cons]
            exact hx
          · intro b₀ rn hinf hall
            exact hrun b₀ rn (hinf.trans (List.infix_cons (List.infix_refl _))) hall
        rw [chainWind_cons₂, chainWind_cons₂, hedge, hrec]

/-- **`chainWind` transport across one shared vertex-height `h`, per-run (`noAdjAtHeight`-free,
dischargeable column).** Public form of `chainWind_cross_one_height_free_aux'`. -/
lemma chainWind_cross_one_height_free' (h : ℝ) (q q' : ℝ × ℝ) (pts : List (ℝ × ℝ))
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h)
    (hchord : chainChordDisjoint q q' pts)
    (hheights : ∀ v ∈ pts, (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h)
    (hhead : ∀ a ∈ pts.head?, a.2 ≠ h)
    (hlast : ∀ a ∈ pts.getLast?, a.2 ≠ h)
    (hrun : ∀ (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)), b₀ :: rn <:+: pts → (∀ v ∈ b₀ :: rn, v.2 = h) →
      Disjoint (segment ℝ q q') (segment ℝ b₀ ((b₀ :: rn).getLast (by simp)))) :
    chainWind pts q = chainWind pts q' :=
  chainWind_cross_one_height_free_aux' h q q' hqh hq'h pts.length pts le_rfl hchord hheights hhead
    hlast hrun

/-- **`loopWind` transport across one shared arc-vertex height `h`, per-run.** Free analogue of
`loopWind_cross_one_height_above`: the `noAdjAtHeight h` hypothesis is replaced by the per-run
disjointness `hrun` (the query `q—q'` misses every height-`h` run's horizontal hull). The horizontal
return edge contributes nothing at either endpoint (`loopWind_eq_chainWind_of_above`), and the open
arc is constant by `chainWind_cross_one_height_free'`. -/
lemma loopWind_cross_one_height_above_free (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (h : ℝ) (q q' : ℝ × ℝ) (hq : y ≤ q.2) (hq' : y ≤ q'.2)
    (hqh : q.2 ≠ h) (hq'h : q'.2 ≠ h)
    (hchord : chainChordDisjoint q q' (arcCorners P y i d))
    (hheights : ∀ v ∈ arcCorners P y i d,
      (∀ p ∈ segment ℝ q q', p.2 ≠ v.2) ∨ v.2 = h)
    (hhead : ∀ a ∈ (arcCorners P y i d).head?, a.2 ≠ h)
    (hlast : ∀ a ∈ (arcCorners P y i d).getLast?, a.2 ≠ h)
    (hrun : ∀ (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)), b₀ :: rn <:+: arcCorners P y i d →
      (∀ v ∈ b₀ :: rn, v.2 = h) →
      Disjoint (segment ℝ q q') (segment ℝ b₀ ((b₀ :: rn).getLast (by simp)))) :
    loopWind P y i d q = loopWind P y i d q' := by
  rw [loopWind_eq_chainWind_of_above P y i d q hq,
    loopWind_eq_chainWind_of_above P y i d q' hq']
  exact chainWind_cross_one_height_free' h q q' (arcCorners P y i d) hqh hq'h hchord hheights hhead
    hlast hrun

/-- **Per-run version of `loopWind_eq_of_monotone_above_aux`.** Same induction, but the
`noAdjAtHeight`-everywhere hypothesis is replaced by the dischargeable per-run hypothesis
`hrunall`: the query `q—q'` misses the horizontal hull `segment b₀ (b₀::rn).getLast` of *every*
equal-height contiguous arc-corner block. Restricts to sub-segments under the height split, and at
the single-height crossing step feeds `loopWind_cross_one_height_above_free`. -/
lemma loopWind_eq_of_monotone_above_aux_free (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ) :
    ∀ (n : ℕ) (q q' : ℝ × ℝ),
      ((arcCorners P y i d).filter
        (fun v => decide (q.2 < v.2 ∧ v.2 < q'.2))).length ≤ n →
      y ≤ q.2 → q.2 < q'.2 →
      chainChordDisjoint q q' (arcCorners P y i d) →
      (∀ v ∈ arcCorners P y i d, q.2 ≠ v.2 ∧ q'.2 ≠ v.2) →
      (∀ (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)), b₀ :: rn <:+: arcCorners P y i d →
        (∀ v ∈ b₀ :: rn, v.2 = b₀.2) →
        Disjoint (segment ℝ q q') (segment ℝ b₀ ((b₀ :: rn).getLast (by simp)))) →
      loopWind P y i d q = loopWind P y i d q' := by
  classical
  intro n
  induction n with
  | zero =>
    intro q q' hlen hq hmono hchord hoff _
    rw [Nat.le_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff] at hlen
    have hseg : chainSegDisjoint q q' (arcCorners P y i d) := by
      apply chainSegDisjoint_of_chord_and_heights hchord
      intro v hv p hp hpv
      have hrange := segment_height_mem q q' p hp
      rw [min_eq_left (le_of_lt hmono), max_eq_right (le_of_lt hmono)] at hrange
      have hne := hoff v hv
      have hl := hlen v hv
      simp only [decide_eq_true_eq, not_and, not_lt] at hl
      rcases lt_or_eq_of_le hrange.1 with h1 | h1
      · rcases lt_or_eq_of_le hrange.2 with h2 | h2
        · rw [hpv] at h1 h2; exact absurd (hl h1) (by linarith)
        · rw [hpv] at h2; exact hne.2 h2.symm
      · rw [hpv] at h1; exact hne.1 h1
    exact loopWind_eq_of_seg_disjoint_above P y i d q q' hq
      (le_of_lt (lt_of_le_of_lt hq hmono)) hseg
  | succ n ih =>
    intro q q' hlen hq hmono hchord hoff hrunall
    by_cases hex : ∃ v ∈ arcCorners P y i d, q.2 < v.2 ∧ v.2 < q'.2
    · obtain ⟨h, hhmem, ⟨hhlo, hhhi⟩, hhmin⟩ :=
        exists_min_pred (L := (arcCorners P y i d).map Prod.snd)
          (P := fun t => q.2 < t ∧ t < q'.2)
          (by obtain ⟨v, hv, hvlo, hvhi⟩ := hex
              exact ⟨v.2, List.mem_map_of_mem hv, hvlo, hvhi⟩)
      set cand : List ℝ :=
        ((arcCorners P y i d).map Prod.snd).filter (fun t => decide (h < t ∧ t < q'.2)) ++ [q'.2]
        with hcand
      have hcand_ne : cand ≠ [] := by rw [hcand]; simp
      have hcand_gt : ∀ t ∈ cand, h < t := by
        intro t ht
        rw [hcand, List.mem_append] at ht
        rcases ht with ht | ht
        · rw [List.mem_filter] at ht; exact (by simpa using ht.2 : h < t ∧ t < q'.2).1
        · simp only [List.mem_singleton] at ht; rw [ht]; linarith
      have hmn : cand.min? ≠ none := by
        rw [Ne, List.min?_eq_none_iff]; exact hcand_ne
      obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hmn
      rw [List.min?_eq_some_iff] at hm'
      obtain ⟨hm'mem, hm'min⟩ := hm'
      have hhm' : h < m' := hcand_gt m' hm'mem
      have hm'leq' : m' ≤ q'.2 := hm'min q'.2 (by rw [hcand]; simp)
      set h' : ℝ := (h + m') / 2 with hh'def
      have hh'lo : h < h' := by rw [hh'def]; linarith
      have hh'hi : h' < m' := by rw [hh'def]; linarith
      have hh'q' : h' < q'.2 := lt_of_lt_of_le hh'hi hm'leq'
      have hqh' : q.2 < h' := lt_trans hhlo hh'lo
      have hno_between : ∀ v ∈ arcCorners P y i d, h < v.2 → v.2 < q'.2 → h' ≤ v.2 := by
        intro v hv hvlo hvhi
        have : v.2 ∈ cand := by
          rw [hcand, List.mem_append]; left
          rw [List.mem_filter]
          exact ⟨List.mem_map_of_mem hv, by simpa using ⟨hvlo, hvhi⟩⟩
        exact le_trans (le_of_lt hh'hi) (hm'min v.2 this)
      have hno_h' : ∀ v ∈ arcCorners P y i d, v.2 ≠ h' := by
        intro v hv hcontra
        have hvlo : h < v.2 := by rw [hcontra]; exact hh'lo
        have hvhi : v.2 < q'.2 := by rw [hcontra]; exact hh'q'
        have hmem : v.2 ∈ cand := by
          rw [hcand, List.mem_append]; left
          rw [List.mem_filter]
          exact ⟨List.mem_map_of_mem hv, by simpa using ⟨hvlo, hvhi⟩⟩
        have := hm'min v.2 hmem
        rw [hcontra] at this; linarith
      obtain ⟨mpt, hmpt_mem, hmpt2, hsub1, hsub2, hle1, hge2⟩ :=
        segment_split_at_height hmono hqh' hh'q'
      -- LOWER piece [q, mpt]: crosses exactly the single height h, free transport
      have hlow : loopWind P y i d q = loopWind P y i d mpt := by
        apply loopWind_cross_one_height_above_free P y i d h q mpt hq (by rw [hmpt2]; linarith)
          (ne_of_lt hhlo) (by rw [hmpt2]; exact ne_of_gt hh'lo)
          (chainChordDisjoint_of_subset hsub1 hchord)
        · intro v hv
          by_cases hvh : v.2 = h
          · exact Or.inr hvh
          · left
            intro p hp hpv
            have hple : p.2 ≤ h' := hle1 p hp
            have hpge : q.2 ≤ p.2 := by
              have := (segment_height_mem q mpt p hp).1
              rwa [min_eq_left (by rw [hmpt2]; linarith)] at this
            have hoffv := hoff v hv
            rw [hpv] at hple hpge
            rcases lt_or_eq_of_le hpge with hlt | heq
            · rcases lt_or_eq_of_le hple with hlt2 | heq2
              · have hvq' : v.2 < q'.2 := lt_trans hlt2 hh'q'
                have hge_h : h ≤ v.2 := hhmin v.2 (List.mem_map_of_mem hv) ⟨hlt, hvq'⟩
                have hvgt : h < v.2 := lt_of_le_of_ne hge_h (Ne.symm hvh)
                have := hno_between v hv hvgt hvq'
                linarith
              · exact hno_h' v hv heq2
            · exact hoffv.1 heq
        · intro a ha
          have ha2 : a.2 = y := by
            simp only [arcCorners, List.head?_cons, Option.mem_some_iff] at ha
            rw [← ha]
          rw [ha2]; exact ne_of_lt (lt_of_le_of_lt hq hhlo)
        · intro a ha
          have ha2 : a.2 = y := by
            have hL : (arcCorners P y i d).getLast? = some (P.edgeThr y (i + (d : ZMod P.n)), y) := by
              unfold arcCorners
              rw [List.getLast?_cons, List.getLast?_concat]; rfl
            rw [hL, Option.mem_some_iff] at ha; rw [← ha]
          rw [ha2]; exact ne_of_lt (lt_of_le_of_lt hq hhlo)
        · -- per-run hull disjointness for height h, restricted to [q, mpt]
          intro b₀ rn hinf hallh
          have hb₀h : b₀.2 = h := hallh b₀ (by simp)
          have hallb : ∀ v ∈ b₀ :: rn, v.2 = b₀.2 := by
            intro v hv; rw [hallh v hv, hb₀h]
          have := hrunall b₀ rn hinf hallb
          exact Set.disjoint_of_subset_left hsub1 this
      -- UPPER piece [mpt, q']: one fewer crossed corner ⟹ IH
      have hupp : loopWind P y i d mpt = loopWind P y i d q' := by
        apply ih mpt q' ?_ (by rw [hmpt2]; linarith) ?_
          (chainChordDisjoint_of_subset hsub2 hchord) ?_ ?_
        · have hwit : ∃ v ∈ arcCorners P y i d, v.2 = h := by
            obtain ⟨v, hv, hv2⟩ := List.mem_map.mp hhmem
            exact ⟨v, hv, hv2⟩
          obtain ⟨vh, hvh_mem, hvh2⟩ := hwit
          have hdrop := length_filter_lt_of_strict (arcCorners P y i d)
            (fun v => decide (q.2 < v.2 ∧ v.2 < q'.2))
            (fun v => decide (mpt.2 < v.2 ∧ v.2 < q'.2))
            (by intro v _ hv2
                simp only [decide_eq_true_eq] at hv2 ⊢
                rw [hmpt2] at hv2
                exact ⟨lt_trans hqh' hv2.1, hv2.2⟩)
            vh hvh_mem
            (by simp only [decide_eq_true_eq]; rw [hvh2]; exact ⟨hhlo, hhhi⟩)
            (by simp only [decide_eq_true_eq, not_and, not_lt]
                intro hlt; rw [hmpt2] at hlt; rw [hvh2] at hlt; linarith)
          omega
        · rw [hmpt2]; exact hh'q'
        · intro v hv
          refine ⟨?_, (hoff v hv).2⟩
          rw [hmpt2]
          exact fun hc => hno_h' v hv hc.symm
        · intro b₀ rn hinf hallb
          have := hrunall b₀ rn hinf hallb
          exact Set.disjoint_of_subset_left hsub2 this
      rw [hlow, hupp]
    · simp only [not_exists, not_and, not_lt] at hex
      have hseg : chainSegDisjoint q q' (arcCorners P y i d) := by
        apply chainSegDisjoint_of_chord_and_heights hchord
        intro v hv p hp hpv
        have hrange := segment_height_mem q q' p hp
        rw [min_eq_left (le_of_lt hmono), max_eq_right (le_of_lt hmono)] at hrange
        have hne := hoff v hv
        rcases lt_or_eq_of_le hrange.1 with h1 | h1
        · rcases lt_or_eq_of_le hrange.2 with h2 | h2
          · rw [hpv] at h1 h2; exact absurd (hex v hv h1) (by linarith)
          · rw [hpv] at h2; exact hne.2 h2.symm
        · rw [hpv] at h1; exact hne.1 h1
      exact loopWind_eq_of_seg_disjoint_above P y i d q q' hq
        (le_of_lt (lt_of_le_of_lt hq hmono)) hseg

/-- **Monotone-above transport of `loopWind`, per-run (`noAdjAtHeight`-free).** Free analogue of
`loopWind_eq_of_monotone_above`: the no-adjacent-equal-height hypothesis is dropped in favour of the
dischargeable per-run hypothesis `hrunall` (the height-monotone query `q—q'` misses every
equal-height contiguous arc-corner block's horizontal hull). -/
lemma loopWind_eq_of_monotone_above_free (P : LatticePolygon) (y : ℝ) (i : ZMod P.n) (d : ℕ)
    (q q' : ℝ × ℝ) (hq : y ≤ q.2) (hq' : y ≤ q'.2) (hne : q.2 ≠ q'.2)
    (hchord : chainChordDisjoint q q' (arcCorners P y i d))
    (hoff : ∀ v ∈ arcCorners P y i d, q.2 ≠ v.2 ∧ q'.2 ≠ v.2)
    (hrunall : ∀ (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)), b₀ :: rn <:+: arcCorners P y i d →
      (∀ v ∈ b₀ :: rn, v.2 = b₀.2) →
      Disjoint (segment ℝ q q') (segment ℝ b₀ ((b₀ :: rn).getLast (by simp)))) :
    loopWind P y i d q = loopWind P y i d q' := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact loopWind_eq_of_monotone_above_aux_free P y i d _ q q' le_rfl hq hlt hchord hoff hrunall
  · refine (loopWind_eq_of_monotone_above_aux_free P y i d _ q' q le_rfl hq' hgt ?_ ?_ ?_).symm
    · exact chainChordDisjoint_of_subset (a := q') (b := q) (by rw [segment_symm]) hchord
    · intro v hv; exact ⟨(hoff v hv).2, (hoff v hv).1⟩
    · intro b₀ rn hinf hallb
      have := hrunall b₀ rn hinf hallb
      rwa [show segment ℝ q' q = segment ℝ q q' from segment_symm ..]

/-- **Same-height segment membership in `uIcc` coordinates.** For two points `a, b` at the
same height (`a.2 = b.2`), a point `p` lies on the segment `a—b` iff it shares their height
and its x-coordinate lies in the unordered interval `[a.1, b.1]`. The segment is horizontal, so
membership reduces to the x-coordinate interval. -/
lemma mem_segment_iff_uIcc_of_eq_snd (a b p : ℝ × ℝ) (hab : a.2 = b.2) :
    p ∈ segment ℝ a b ↔ (p.2 = a.2 ∧ p.1 ∈ Set.uIcc a.1 b.1) := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← hab]
    have key2 : s * a.2 + t * a.2 = a.2 := by rw [← add_mul, hst, one_mul]
    have keyx : s * a.1 + t * b.1 = a.1 + t * (b.1 - a.1) := by
      have : s = 1 - t := by linarith
      rw [this]; ring
    refine ⟨by linarith [key2], ?_⟩
    rw [Set.mem_uIcc, keyx]
    rcases le_total a.1 b.1 with h | h
    · left; constructor
      · nlinarith [mul_nonneg ht (by linarith : (0:ℝ) ≤ b.1 - a.1)]
      · nlinarith [mul_le_mul_of_nonneg_left h ht, hst, hs]
    · right; constructor
      · nlinarith [mul_nonneg ht (by linarith : (0:ℝ) ≤ a.1 - b.1), hst, hs]
      · nlinarith [mul_nonneg ht (by linarith : (0:ℝ) ≤ a.1 - b.1)]
  · rintro ⟨hp2, hp1⟩
    rw [Set.mem_uIcc] at hp1
    rcases eq_or_ne a.1 b.1 with hx | hx
    · have hpa : p = a := by
        apply Prod.ext
        · rcases hp1 with ⟨h1,h2⟩|⟨h1,h2⟩
          · linarith
          · linarith [hx]
        · exact hp2
      rw [hpa]; exact left_mem_segment _ _ _
    · set t := (p.1 - a.1) / (b.1 - a.1) with ht
      have hbma : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have htge : 0 ≤ t := by
        rw [ht]; rcases lt_or_gt_of_ne hbma with hlt | hgt
        · rw [div_nonneg_iff]; rcases hp1 with ⟨h1,h2⟩|⟨h1,h2⟩
          · nlinarith
          · right; constructor <;> linarith
        · rw [div_nonneg_iff]; rcases hp1 with ⟨h1,h2⟩|⟨h1,h2⟩
          · left; constructor <;> linarith
          · nlinarith
      have htle : t ≤ 1 := by
        rw [ht]; rcases lt_or_gt_of_ne hbma with hlt | hgt
        · rw [div_le_one_of_neg hlt]; rcases hp1 with ⟨h1,h2⟩|⟨h1,h2⟩ <;> linarith
        · rw [div_le_one hgt]; rcases hp1 with ⟨h1,h2⟩|⟨h1,h2⟩ <;> linarith
      refine ⟨1 - t, t, by linarith, htge, by ring, ?_⟩
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; rw [ht]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [hp2, ← hab]; ring

/-- **An interior point splits a `uIcc`.** The unordered interval `[a, b]` is covered by the
two sub-intervals `[a, m]` and `[m, b]` for any `m`: the point `m` partitions the line, so any
`x` between `a` and `b` is between `a` and `m` or between `m` and `b`. -/
lemma uIcc_subset_union_uIcc (a m b : ℝ) :
    Set.uIcc a b ⊆ Set.uIcc a m ∪ Set.uIcc m b := by
  intro x hx
  rw [Set.mem_uIcc] at hx
  simp only [Set.mem_union, Set.mem_uIcc]
  rcases le_total x m with hxm | hxm
  · rcases hx with ⟨h1,h2⟩|⟨h1,h2⟩
    · exact Or.inl (Or.inl ⟨h1, hxm⟩)
    · exact Or.inr (Or.inr ⟨h1, hxm⟩)
  · rcases hx with ⟨h1,h2⟩|⟨h1,h2⟩
    · exact Or.inr (Or.inl ⟨hxm, h2⟩)
    · exact Or.inl (Or.inr ⟨hxm, h2⟩)

/-- **Hull of a horizontal run is disjoint from a query avoiding its chords and corners.** If
`b₀ :: rn` is a list of points all at the same height `c`, the query segment `q—q'` misses every
consecutive chord (`chainChordDisjoint`), and `q—q'` avoids every corner of the run, then `q—q'`
is disjoint from the whole horizontal hull `segment b₀ ((b₀::rn).getLast)`. The hull is covered
by the consecutive chords together with the run's corners (the degenerate singleton case), so a
query missing all of those misses the hull. This is the connector that discharges the per-run
hypothesis `hrunall` of `loopWind_eq_of_monotone_above_free` from per-chord disjointness plus the
"query off the arc corners" fact (`hoff`). -/
lemma run_hull_disjoint_of_chainChordDisjoint (q q' : ℝ × ℝ) (c : ℝ) :
    ∀ (b₀ : ℝ × ℝ) (rn : List (ℝ × ℝ)),
      (∀ v ∈ b₀ :: rn, v.2 = c) →
      (∀ v ∈ b₀ :: rn, v ∉ segment ℝ q q') →
      chainChordDisjoint q q' (b₀ :: rn) →
      Disjoint (segment ℝ q q') (segment ℝ b₀ ((b₀ :: rn).getLast (by simp))) := by
  intro b₀ rn
  induction rn generalizing b₀ with
  | nil =>
    intro _ hpts _
    simp only [List.getLast_singleton]
    rw [Set.disjoint_left]
    intro p hp hpseg
    rw [segment_same, Set.mem_singleton_iff] at hpseg
    rw [hpseg] at hp
    exact hpts b₀ (by simp) hp
  | cons b₁ rn' ih =>
    intro hc hpts hcd
    have hb₀ : b₀.2 = c := hc b₀ (by simp)
    have hb₁ : b₁.2 = c := hc b₁ (by simp)
    have hcd' := (chainChordDisjoint_cons₂ q q' b₀ b₁ rn').mp hcd
    have hchord01 : Disjoint (segment ℝ q q') (segment ℝ b₀ b₁) := by
      rw [Set.disjoint_left]; intro p hp hps; exact hcd'.1 p hp hps
    have hctail : ∀ v ∈ b₁ :: rn', v.2 = c := fun v hv => hc v (by simp [hv])
    have hptstail : ∀ v ∈ b₁ :: rn', v ∉ segment ℝ q q' := fun v hv => hpts v (by simp [hv])
    have hrec : Disjoint (segment ℝ q q')
        (segment ℝ b₁ ((b₁ :: rn').getLast (by simp))) := ih b₁ hctail hptstail hcd'.2
    set last := (b₁ :: rn').getLast (by simp) with hlast
    have hlastc : last.2 = c := hctail last (by rw [hlast]; exact List.getLast_mem _)
    have hgetlast : ((b₀ :: b₁ :: rn').getLast (by simp)) = last := by
      rw [hlast]; rw [List.getLast_cons_cons]
    rw [hgetlast]
    rw [Set.disjoint_left]
    intro p hp hpseg
    -- p ∈ segment b₀ last : decode into height + uIcc
    rw [mem_segment_iff_uIcc_of_eq_snd b₀ last p (by rw [hb₀, hlastc])] at hpseg
    obtain ⟨hp2, hp1⟩ := hpseg
    -- split uIcc b₀.1 last.1 ⊆ uIcc b₀.1 b₁.1 ∪ uIcc b₁.1 last.1
    have hsplit := uIcc_subset_union_uIcc b₀.1 b₁.1 last.1 hp1
    rcases hsplit with h01 | h1l
    · have : p ∈ segment ℝ b₀ b₁ := by
        rw [mem_segment_iff_uIcc_of_eq_snd b₀ b₁ p (by rw [hb₀, hb₁])]
        exact ⟨hp2, h01⟩
      exact Set.disjoint_left.mp hchord01 hp this
    · have : p ∈ segment ℝ b₁ last := by
        rw [mem_segment_iff_uIcc_of_eq_snd b₁ last p (by rw [hb₁, hlastc])]
        exact ⟨by rw [hp2, hb₀, hb₁], h1l⟩
      exact Set.disjoint_left.mp hrec hp this

/-- **A small offset avoiding finitely many forbidden heights.** Given any positive bound `δ`
and a finite set `S` of forbidden real values, there is `ε` with `0 < ε ≤ δ` such that the
shifted height `y + ε` avoids every value in `S`. The open interval `Ioo 0 δ` is infinite,
while the preimage `{ε | y + ε ∈ S}` is finite (injective shift of a finite set), so some
`ε ∈ Ioo 0 δ` escapes it. This is the genericity selector for the climbing-leg argument: it
lets us pick the slab height `y + ε` small enough for `loopWind_just_above_segment` while
keeping `y + ε` and the partial-edge endpoints off all finitely many arc-vertex heights. -/
lemma exists_eps_avoiding_finset (y δ : ℝ) (hδ : 0 < δ) (S : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ y + ε ∉ S := by
  by_contra h
  push_neg at h
  -- every ε in (0, δ] gives y + ε ∈ S
  have hsub : Set.Ioc (0:ℝ) δ ⊆ (fun ε => y + ε) ⁻¹' (S : Set ℝ) := by
    intro ε hε
    exact h ε hε.1 hε.2
  have hfin : ((fun ε => y + ε) ⁻¹' (S : Set ℝ)).Finite := by
    apply Set.Finite.preimage _ S.finite_toSet
    intro a _ b _ hab; simpa using hab
  have hIoc : (Set.Ioc (0:ℝ) δ).Finite := hfin.subset hsub
  exact (Set.Ioc_infinite hδ) hIoc

/-- **`chainChordDisjoint` from a consecutive-pair chain.** If every consecutive pair `(a, b)`
of the polyline `L` has its chord `segment ℝ a b` avoided by the whole query segment `q—q'`
(packaged as `List.IsChain` of the chord-avoidance relation), then `chainChordDisjoint q q' L`
holds. This is the constructor that builds the per-chord disjointness hypothesis consumed by the
monotone-above `loopWind` transport from a uniform "each chord misses `q—q'`" fact, peeling the
list head by head via `chainChordDisjoint_cons₂`. -/
lemma chainChordDisjoint_of_isChain (q q' : ℝ × ℝ) (L : List (ℝ × ℝ))
    (h : L.IsChain (fun a b => ∀ p ∈ segment ℝ q q', p ∉ segment ℝ a b)) :
    chainChordDisjoint q q' L := by
  induction L with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest' =>
      rw [List.isChain_cons_cons] at h
      exact (chainChordDisjoint_cons₂ q q' a b rest').mpr ⟨h.1, ih h.2⟩

/-- **`chainOffCross` from a consecutive-pair chain.** If every consecutive pair `(a, b)` of the
polyline `L` has its ray-crossing locus `cross (b - a) (· - a) = 0` avoided by the whole query
segment `q—q'` (packaged as `List.IsChain` of the off-cross relation), then `chainOffCross q q' L`
holds. This is the constructor that builds the horizontal-transport hypothesis consumed by
`loopWind_eq_of_offCross` from a uniform "each edge's crossing locus misses `q—q'`" fact. -/
lemma chainOffCross_of_isChain (q q' : ℝ × ℝ) (L : List (ℝ × ℝ))
    (h : L.IsChain (fun a b => ∀ p ∈ segment ℝ q q', cross (b - a) (p - a) ≠ 0)) :
    chainOffCross q q' L := by
  induction L with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest' =>
      rw [List.isChain_cons_cons] at h
      exact (chainOffCross_cons₂ q q' a b rest').mpr ⟨h.1, ih h.2⟩
