import Submission.Jordan
import Submission.PerEdge

/-!
# Pick's theorem: reductions (winding lemmas, local constancy, provider reduction)

Module 1 of the split `Pick.lean`. Contains the namespace `Pick` block with the
winding lemmas, local constancy, `pick_of_provider`, and the reduction of
`winding ∈ {0,1}` to interleaving.
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
    (hdisj : ∀ᵐ q ∂MeasureTheory.volume,
      ¬((deleteLast P h).winding q = 1 ∧ (earTri P m hm).winding q = 1)) :
    ∀ᵐ q ∂MeasureTheory.volume, P.winding q = 0 ∨ P.winding q = 1 := by
  filter_upwards [hdL, hear, hdisj] with q hq1 hq2 hqd
  rw [winding_eq_deleteLast_add_earTri P h m hm q]
  rcases hq1 with h0 | h1 <;> rcases hq2 with h0' | h1'
  · omega
  · omega
  · omega
  · exact absurd ⟨h1, h1'⟩ hqd

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
    (hdisj : ∀ᵐ q ∂MeasureTheory.volume,
      ¬((deleteLast P h).winding q = 1 ∧ (earTri P m hm).winding q = 1))
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
    (∀ᵐ q ∂MeasureTheory.volume,
      ¬((deleteLast R h2).winding q = 1 ∧ (earTri R m hm).winding q = 1)) ∧
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

/-- **Vertices are distinct (general `n`).** In a simple polygon, the vertex map is
injective: `P.vert i = P.vert j → i = j`. If `i ≠ j`, the shared point would force
two edges to meet illegally — `vert_notMem_edgeSeg` (non-adjacent/far-adjacent) or
the nondegeneracy clause `hsimple.1` (the `j = i-1` adjacent case). -/
lemma vert_injective (P : LatticePolygon) (hsimple : P.IsSimple) :
    Function.Injective P.vert := by
  intro i j hij
  by_contra hne
  have hp : toReal (P.vert i) = toReal (P.vert j) := by rw [hij]
  by_cases hji1 : j = i - 1
  · subst hji1
    have hcyc : i - 1 + 1 = i := by ring
    exact hsimple.1 (i - 1) (by rw [hcyc]; exact (toReal_injective hp).symm)
  · have hmem : toReal (P.vert i) ∈ P.edgeSeg j := by
      rw [hp, LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _
    exact vert_notMem_edgeSeg P hsimple i j (Ne.symm hne) hji1 hmem

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

/-- **Positive distance from a vertex to the non-incident edges (`infDist` form).**
For a vertex `v = P.vert m` and any single edge `j` not incident to `v`
(`j ≠ m`, `j ≠ m-1`), the infimum distance from `v` to the (compact, hence closed)
segment `edgeSeg j` is strictly positive, because `v ∉ edgeSeg j` (`vert_notMem_edgeSeg`).
The `infDist` restatement of `exists_isolating_ball` for a single non-incident edge —
the foundational clearance fact behind the apex-clearance/box primitives. -/
lemma vertex_infDist_pos (P : LatticePolygon) (hsimple : P.IsSimple) (m j : ZMod P.n)
    (hjm : j ≠ m) (hjm1 : j ≠ m - 1) :
    0 < Metric.infDist (toReal (P.vert m)) (P.edgeSeg j) := by
  have hclosed : IsClosed (P.edgeSeg j) := (isCompact_edgeSeg P j).isClosed
  have hne : (P.edgeSeg j).Nonempty :=
    ⟨toReal (P.vert j), by rw [LatticePolygon.edgeSeg]; exact left_mem_segment ℝ _ _⟩
  rw [← hclosed.notMem_iff_infDist_pos hne]
  exact vert_notMem_edgeSeg P hsimple m j hjm hjm1

/-- **A small box around a vertex meets the boundary only on the two incident edges.**
For a vertex `v = P.vert k = (xv, w)`, there is `ε > 0` such that every boundary point
inside the open box `(xv−ε, xv+ε) × (w−ε, w+ε)` lies on one of the two edges incident
to `v`, namely `edgeSeg (k-1)` (`vert(k-1) → v`) or `edgeSeg k` (`v → vert(k+1)`). Proof:
take the isolating radius `r` of `exists_isolating_ball` (every *non-incident* edge is
`Disjoint` from the ball of radius `r`); choose `ε := r/2`, so the box sits inside the
ball (sup-metric); a boundary point in the box lies on some `edgeSeg j`, and if `j` were
non-incident it would contradict the disjointness. This is the local reduction of the
boundary near `v` to its two incident chords — the geometric core that gates the
apex-clearance routing move (`route_around_chord_end`). -/
lemma box_meets_only_incident_edges (P : LatticePolygon) (hsimple : P.IsSimple)
    (k : ZMod P.n) :
    ∃ ε > 0, ∀ q : ℝ × ℝ,
      q ∈ Set.Ioo ((toReal (P.vert k)).1 - ε) ((toReal (P.vert k)).1 + ε) ×ˢ
            Set.Ioo ((toReal (P.vert k)).2 - ε) ((toReal (P.vert k)).2 + ε) →
      q ∈ P.boundary →
      q ∈ P.edgeSeg (k - 1) ∪ P.edgeSeg k := by
  obtain ⟨r, hr, hball⟩ := exists_isolating_ball P hsimple k
  refine ⟨r / 2, by linarith, ?_⟩
  rintro q ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ hqb
  obtain ⟨_, ⟨j, rfl⟩, hqj⟩ := hqb
  -- q is within the ball of radius r around v
  have hqball : q ∈ Metric.ball (toReal (P.vert k)) r := by
    rw [Metric.mem_ball, dist_comm, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor <;> rw [abs_lt] <;> constructor <;> linarith
  by_cases hjk : j = k
  · subst hjk; exact Or.inr hqj
  · by_cases hjk1 : j = k - 1
    · subst hjk1; exact Or.inl hqj
    · exact absurd (Set.disjoint_left.mp (hball j hjk hjk1) hqball) (not_not.mpr hqj)

/-- **Apex clearance below a local-min vertex.** At a vertex `v = P.vert k = (xv, w)`
that is a strict local minimum in height — both neighbours `vert (k-1)` and `vert (k+1)`
lie strictly above `w` — there is `δ > 0` such that the half-open box just *below* `w`,
`(xv−δ, xv+δ) × (w−δ, w)`, is entirely off the boundary. Proof: by
`box_meets_only_incident_edges` the only boundary inside the full box `(xv−δ,xv+δ)×(w−δ,w+δ)`
comes from the two incident edges `edgeSeg (k-1)` and `edgeSeg k`; both of these have *both*
endpoints at height `≥ w` (their shared endpoint is `v` at height `w`, the other endpoints
above `w`), so every point of either incident edge sits at height `≥ w`. Hence strictly
below `w` the box meets no boundary. This is the local apex-clearance primitive: a vertical
probe just to either side of `xv`, approaching `v` from below, stays off the boundary — the
geometric fact that gates the cross-vertex routing move `route_around_chord_end`. -/
lemma exists_clear_below_local_min (P : LatticePolygon) (hsimple : P.IsSimple) (k : ZMod P.n)
    (hkm1 : (toReal (P.vert k)).2 < (toReal (P.vert (k - 1))).2)
    (hkp1 : (toReal (P.vert k)).2 < (toReal (P.vert (k + 1))).2) :
    ∃ δ > 0, ∀ q : ℝ × ℝ,
      q.1 ∈ Set.Ioo ((toReal (P.vert k)).1 - δ) ((toReal (P.vert k)).1 + δ) →
      q.2 ∈ Set.Ioo ((toReal (P.vert k)).2 - δ) (toReal (P.vert k)).2 →
      q ∉ P.boundary := by
  set v := toReal (P.vert k) with hv
  set w := v.2 with hw
  obtain ⟨ε, hε, hbox⟩ := box_meets_only_incident_edges P hsimple k
  refine ⟨ε, hε, ?_⟩
  rintro q ⟨hq1, hq2⟩ ⟨hq3, hq4⟩ hqb
  have hqbox : q ∈ Set.Ioo (v.1 - ε) (v.1 + ε) ×ˢ Set.Ioo (w - ε) (w + ε) :=
    ⟨⟨hq1, hq2⟩, ⟨hq3, by linarith⟩⟩
  have e1 : (toReal (P.vert (k - 1 + 1))).2 = w := by
    have : k - 1 + 1 = k := by ring
    rw [this]
  have hge : w ≤ q.2 := by
    rcases hbox q hqbox hqb with hc | hc
    · rw [LatticePolygon.edgeSeg, segment_eq_image] at hc
      obtain ⟨t, ht, rfl⟩ := hc
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [ht.1, ht.2, hkm1, e1]
    · rw [LatticePolygon.edgeSeg, segment_eq_image] at hc
      obtain ⟨t, ht, rfl⟩ := hc
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [ht.1, ht.2, hkp1]
  linarith

/-- **Apex clearance above a local-max vertex.** Mirror of `exists_clear_below_local_min`:
at a strict local *maximum* vertex `v = P.vert k = (xv, w)` (both neighbours strictly below
`w`), the half-open box just *above* `w`, `(xv−δ, xv+δ) × (w, w+δ)`, is off the boundary.
The two incident edges have both endpoints at height `≤ w`, so every point of either lies at
height `≤ w`; strictly above `w` the box is boundary-free. -/
lemma exists_clear_above_local_max (P : LatticePolygon) (hsimple : P.IsSimple) (k : ZMod P.n)
    (hkm1 : (toReal (P.vert (k - 1))).2 < (toReal (P.vert k)).2)
    (hkp1 : (toReal (P.vert (k + 1))).2 < (toReal (P.vert k)).2) :
    ∃ δ > 0, ∀ q : ℝ × ℝ,
      q.1 ∈ Set.Ioo ((toReal (P.vert k)).1 - δ) ((toReal (P.vert k)).1 + δ) →
      q.2 ∈ Set.Ioo (toReal (P.vert k)).2 ((toReal (P.vert k)).2 + δ) →
      q ∉ P.boundary := by
  set v := toReal (P.vert k) with hv
  set w := v.2 with hw
  obtain ⟨ε, hε, hbox⟩ := box_meets_only_incident_edges P hsimple k
  refine ⟨ε, hε, ?_⟩
  rintro q ⟨hq1, hq2⟩ ⟨hq3, hq4⟩ hqb
  have hqbox : q ∈ Set.Ioo (v.1 - ε) (v.1 + ε) ×ˢ Set.Ioo (w - ε) (w + ε) :=
    ⟨⟨hq1, hq2⟩, ⟨by linarith, hq4⟩⟩
  have e1 : (toReal (P.vert (k - 1 + 1))).2 = w := by
    have : k - 1 + 1 = k := by ring
    rw [this]
  have hle : q.2 ≤ w := by
    rcases hbox q hqbox hqb with hc | hc
    · rw [LatticePolygon.edgeSeg, segment_eq_image] at hc
      obtain ⟨t, ht, rfl⟩ := hc
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [ht.1, ht.2, hkm1, e1]
    · rw [LatticePolygon.edgeSeg, segment_eq_image] at hc
      obtain ⟨t, ht, rfl⟩ := hc
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [ht.1, ht.2, hkp1]
  linarith

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
