import Submission.EvalBridgeBoundary

/-!
# Bridge obligation: simplicity conversion

The eval `IsSimple (latPoly v)` (Mathlib `Polygon.HasNondegenerateEdges` + the
disjointness clauses on `edgeSet`) implies our `(ourPoly hn v).IsSimple`
(the three `edgeSeg`-based clauses).  The per-edge correspondence
`edgeSet ℝ (latPoly v) i = (ourPoly hn v).edgeSeg ↑i` is the same identification
used in `boundary_bridge`.
-/

namespace LeanEval.Geometry.PicksTheorem

open MeasureTheory

/-- **Bridge obligation — simplicity conversion.** -/
theorem ourPoly_isSimple {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    (ourPoly hn v).IsSimple := by
  haveI : NeZero n := ⟨hn.ne'⟩
  -- index algebra: `val` of a cast-successor (re-derived from `boundary_bridge`),
  -- stated at the polygon's own modulus to match the `IsSimple` binders
  have val_succ : ∀ i : Fin n,
      ((i.val : ZMod (ourPoly hn v).n) + 1).val = (i + 1).val := by
    intro i
    show ((i.val : ZMod n) + 1).val = (i + 1).val
    have h : (i.val : ZMod n) + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; ring
    rw [h, ZMod.val_natCast, Fin.val_add, Fin.val_one']
    conv_rhs => rw [Nat.add_mod]
    simp
  -- `finRotate` in `ZMod` is `+1`
  have hsucc : ∀ i : Fin n,
      ((finRotate n i).val : ZMod (ourPoly hn v).n)
        = (i.val : ZMod (ourPoly hn v).n) + 1 := by
    intro i
    rw [finRotate_apply, ← val_succ i, ZMod.natCast_zmod_val]
  -- `ourPoly` vertex at the cast index is the original `v`
  have hvert : ∀ i : Fin n,
      (ourPoly hn v).vert (↑i.val : ZMod (ourPoly hn v).n) = v i := by
    intro i
    rw [ourPoly_vert]
    congr 1
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  -- the per-edge identification (same as in `boundary_bridge`)
  have hedge : ∀ i : Fin n,
      (latPoly v).edgeSet ℝ i = (ourPoly hn v).edgeSeg (↑i.val : ZMod (ourPoly hn v).n) := by
    intro i
    show affineSegment ℝ (toPlane (v i)) (toPlane (v (finRotate n i)))
        = (ourPoly hn v).edgeSeg (↑i.val : ZMod (ourPoly hn v).n)
    rw [affineSegment_eq_segment, Pick.LatticePolygon.edgeSeg]
    simp only [ourPoly_vert]
    congr 1
    · show Pick.toReal (v i) = Pick.toReal _
      congr 2
      apply Fin.ext
      exact (ZMod.val_natCast_of_lt i.isLt).symm
    · show Pick.toReal (v (finRotate n i)) = Pick.toReal _
      congr 2
      apply Fin.ext
      rw [finRotate_apply]
      exact (val_succ i).symm
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1: nondegenerate edges
    intro j
    set i : Fin n := ⟨j.val, ZMod.val_lt j⟩ with hi
    have hij : (↑i.val : ZMod (ourPoly hn v).n) = j := ZMod.natCast_zmod_val j
    have hjv : (ourPoly hn v).vert j = v i := by rw [← hij]; exact hvert i
    have hj1v : (ourPoly hn v).vert (j + 1) = v (finRotate n i) := by
      rw [← hvert (finRotate n i), hsucc i, hij]
    intro heq
    apply hsimple.1 i
    show toPlane (v i) = toPlane (v (finRotate n i))
    rw [← hjv, ← hj1v, heq]
  · -- clause 2: non-adjacent edges disjoint
    intro a b hab hab1 hba1
    set ia : Fin n := ⟨a.val, ZMod.val_lt a⟩ with hia
    set ib : Fin n := ⟨b.val, ZMod.val_lt b⟩ with hib
    have hva : (↑ia.val : ZMod (ourPoly hn v).n) = a := ZMod.natCast_zmod_val a
    have hvb : (↑ib.val : ZMod (ourPoly hn v).n) = b := ZMod.natCast_zmod_val b
    have hne : ia ≠ ib := by
      intro h; apply hab; rw [← hva, ← hvb, h]
    have hnadj : ¬ Adjacent ia ib := by
      rintro (h | h)
      · apply hab1; rw [← hvb, ← h, hsucc ia, hva]
      · apply hba1; rw [← hva, ← h, hsucc ib, hvb]
    have hdis := hsimple.2.1 ia ib hne hnadj
    rwa [hedge ia, hedge ib, hva, hvb] at hdis
  · -- clause 3: adjacent edges meet at the shared vertex
    intro a
    set ia : Fin n := ⟨a.val, ZMod.val_lt a⟩ with hia
    have hva : (↑ia.val : ZMod (ourPoly hn v).n) = a := ZMod.natCast_zmod_val a
    have hrot : (↑(finRotate n ia).val : ZMod (ourPoly hn v).n) = a + 1 := by
      rw [hsucc ia, hva]
    have h3 := hsimple.2.2 ia
    rw [hedge ia, hva, hedge (finRotate n ia), hrot] at h3
    rw [h3]
    congr 1
    show Pick.toReal (v (finRotate n ia)) = Pick.toReal ((ourPoly hn v).vert (a + 1))
    rw [show (a + 1 : ZMod (ourPoly hn v).n) = ↑(finRotate n ia).val from hrot.symm,
      hvert (finRotate n ia)]

end LeanEval.Geometry.PicksTheorem
