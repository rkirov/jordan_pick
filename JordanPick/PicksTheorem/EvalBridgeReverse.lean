import JordanPick.PicksTheorem.Pick

/-!
# Reversal lemmas for `reverseP` needed by the eval bridge

`reverseP P` reverses the vertex order (`vert i = P.vert (-i)`).  It already has
`reverseP_shoelace : (reverseP P).shoelace = - P.shoelace`.  The eval bridge also
needs that reversal preserves the boundary set and simplicity, and negates the
winding number — so the *positively-oriented* representative `reverseP P`
(used when `P.shoelace < 0`) has the same `inside`/lattice data as `P` with the
sign of the interior flipped.
-/

namespace Pick

namespace LatticePolygon

variable (P : LatticePolygon)

/-- **Per-edge winding antisymmetry.** Swapping the endpoints of a directed edge
negates its winding contribution.  The two `edgeWind` branches are mutually
exclusive, and swapping the endpoints negates the `cross` term
(`cross (a-b) (q-b) = - cross (b-a) (q-a)`), which exactly swaps the two
branches. -/
private lemma edgeWind_swap (a b q : ℝ × ℝ) : edgeWind b a q = - edgeWind a b q := by
  have hC : cross (a - b) (q - b) = - cross (b - a) (q - a) := by
    unfold cross; simp only [Prod.fst_sub, Prod.snd_sub]; ring
  rcases edgeWind_mem a b q with h | h | h
  · -- `edgeWind a b q = -1`
    rw [h, neg_neg]
    have hh := (edgeWind_eq_neg_one_iff a b q).mp h
    rw [edgeWind_eq_one_iff b a q]
    obtain ⟨h1, h2, h3⟩ := hh
    exact ⟨h1, h2, by rw [hC]; linarith⟩
  · -- `edgeWind a b q = 0`
    rw [h, neg_zero]
    rcases edgeWind_mem b a q with h' | h' | h'
    · exfalso
      obtain ⟨k1, k2, k3⟩ := (edgeWind_eq_neg_one_iff b a q).mp h'
      have hone : edgeWind a b q = 1 :=
        (edgeWind_eq_one_iff a b q).mpr ⟨k1, k2, by rw [hC] at k3; linarith⟩
      rw [hone] at h; exact absurd h (by decide)
    · exact h'
    · exfalso
      obtain ⟨k1, k2, k3⟩ := (edgeWind_eq_one_iff b a q).mp h'
      have hneg : edgeWind a b q = -1 :=
        (edgeWind_eq_neg_one_iff a b q).mpr ⟨k1, k2, by rw [hC] at k3; linarith⟩
      rw [hneg] at h; exact absurd h (by decide)
  · -- `edgeWind a b q = 1`
    rw [h]
    have hh := (edgeWind_eq_one_iff a b q).mp h
    rw [edgeWind_eq_neg_one_iff b a q]
    obtain ⟨h1, h2, h3⟩ := hh
    exact ⟨h1, h2, by rw [hC]; linarith⟩

/-- Edge `i` of `reverseP P` is edge `-i-1` of `P` (the same segment, reversed). -/
private lemma reverseP_edgeSeg (i : ZMod P.n) :
    (reverseP P).edgeSeg i = P.edgeSeg (-i - 1) := by
  simp only [LatticePolygon.edgeSeg, reverseP_vert]
  rw [segment_symm]
  congr 1
  · exact congrArg (fun k => toReal (P.vert k)) (by ring : (-(i + 1) : ZMod P.n) = -i - 1)
  · exact congrArg (fun k => toReal (P.vert k)) (by ring : (-i : ZMod P.n) = -i - 1 + 1)

/-- Reversal preserves the boundary set (same segments, traversed backwards). -/
theorem reverseP_boundary : (reverseP P).boundary = P.boundary := by
  show (⋃ i : ZMod P.n, (reverseP P).edgeSeg i) = ⋃ i : ZMod P.n, P.edgeSeg i
  simp only [reverseP_edgeSeg]
  have hsurj : Function.Surjective (fun i : ZMod P.n => -i - 1) := by
    intro y; exact ⟨-y - 1, by ring⟩
  rw [← hsurj.iUnion_comp (fun y => P.edgeSeg y)]

/-- Reversal negates the winding number. -/
theorem reverseP_winding (q : ℝ × ℝ) : (reverseP P).winding q = - P.winding q := by
  have hsum : (∑ i : ZMod P.n,
        edgeWind (toReal (P.vert (-i))) (toReal (P.vert (-(i + 1)))) q)
      = - ∑ i, edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q := by
    have h1 : (∑ i : ZMod P.n,
          edgeWind (toReal (P.vert (-i))) (toReal (P.vert (-(i + 1)))) q)
        = ∑ i : ZMod P.n, edgeWind (toReal (P.vert i)) (toReal (P.vert (i - 1))) q := by
      rw [← Equiv.sum_comp (Equiv.neg (ZMod P.n))
        (fun i => edgeWind (toReal (P.vert i)) (toReal (P.vert (i - 1))) q)]
      apply Finset.sum_congr rfl; intro i _
      simp only [Equiv.neg_apply]
      have : -(i + 1) = -i - 1 := by ring
      rw [this]
    rw [h1]
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n))
      (fun i => edgeWind (toReal (P.vert i)) (toReal (P.vert (i - 1))) q)]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [Equiv.coe_addRight]
    have e : i + 1 - 1 = i := by ring
    rw [e]
    exact edgeWind_swap (toReal (P.vert i)) (toReal (P.vert (i + 1))) q
  show (∑ i : ZMod P.n,
      edgeWind (toReal (P.vert (-i))) (toReal (P.vert (-(i + 1)))) q) = - P.winding q
  rw [hsum]; rfl

/-- Reversal preserves simplicity. -/
theorem reverseP_isSimple (hS : P.IsSimple) : (reverseP P).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · -- no degenerate edge
    show ∀ i : ZMod P.n, (reverseP P).vert i ≠ (reverseP P).vert ((i + 1 : ZMod P.n))
    intro i
    simp only [reverseP_vert]
    have hne := hS.1 (-i - 1)
    have e : (-i - 1) + 1 = -i := by ring
    rw [e] at hne
    have e2 : -(i + 1) = -i - 1 := by ring
    rw [e2]
    exact hne.symm
  · -- non-adjacent edges are disjoint
    show ∀ i j : ZMod P.n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      Disjoint ((reverseP P).edgeSeg i) ((reverseP P).edgeSeg j)
    intro i j hij hi1j hj1i
    simp only [reverseP_edgeSeg]
    exact hS.2.1 (-i - 1) (-j - 1)
      (fun h => hij (by linear_combination -h))
      (fun h => hj1i (by linear_combination h))
      (fun h => hi1j (by linear_combination h))
  · -- consecutive edges meet exactly at their shared vertex
    show ∀ i : ZMod P.n, (reverseP P).edgeSeg i ∩ (reverseP P).edgeSeg ((i + 1 : ZMod P.n)) =
      {toReal ((reverseP P).vert ((i + 1 : ZMod P.n)))}
    intro i
    simp only [reverseP_edgeSeg, reverseP_vert]
    have e1 : (-(i + 1) - 1 : ZMod P.n) = -i - 2 := by ring
    have e2 : (-i - 1 : ZMod P.n) = -i - 2 + 1 := by ring
    have e3 : (-(i + 1) : ZMod P.n) = -i - 2 + 1 := by ring
    rw [e1, e2, e3, Set.inter_comm]
    exact hS.2.2 (-i - 2)

end LatticePolygon

end Pick
