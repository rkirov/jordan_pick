import JordanPick.PicksTheorem.EvalBridge

/-!
# Bridge obligation: boundary match (mechanical)

`(latPoly v).boundary (R := ℝ) = (ourPoly hn v).boundary`.

Mathlib: `Polygon.boundary R poly = ⋃ i, affineSegment R (poly.vertices i) (poly.vertices (finRotate n i))`.
Ours: `LatticePolygon.boundary = ⋃ i, segment ℝ (toReal (vert i)) (toReal (vert (i+1)))`.
Match via `Fin n ↔ ZMod n` reindex, `affineSegment = segment`, `finRotate = (·+1)`,
`toPlane = Pick.toReal`.
-/

namespace LeanEval.Geometry.PicksTheorem

open MeasureTheory

private lemma val_natCast_succ {m : ℕ} [NeZero m] (i : Fin m) :
    ((i.val : ZMod m) + 1).val = (i + 1).val := by
  have h : (i.val : ZMod m) + 1 = ((i.val + 1 : ℕ) : ZMod m) := by push_cast; ring
  rw [h, ZMod.val_natCast, Fin.val_add, Fin.val_one']
  conv_rhs => rw [Nat.add_mod]
  simp

/-- **Bridge obligation — boundary match.** -/
theorem boundary_bridge {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ) :
    (latPoly v).boundary (R := ℝ) = (ourPoly hn v).boundary := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ i : Fin n,
      affineSegment ℝ (toPlane (v i)) (toPlane (v (finRotate n i)))
        = (ourPoly hn v).edgeSeg (i.val : ZMod n) := by
    intro i
    rw [affineSegment_eq_segment, Pick.LatticePolygon.edgeSeg]
    simp only [ourPoly_vert]
    congr 1
    · show Pick.toReal (v i) = Pick.toReal _
      congr 2
      apply Fin.ext
      simp [ZMod.val_natCast_of_lt i.isLt]
    · show Pick.toReal (v (finRotate n i)) = Pick.toReal _
      congr 2
      apply Fin.ext
      rw [finRotate_apply]
      exact (val_natCast_succ i).symm
  have hL : Polygon.boundary ℝ (latPoly v)
      = ⋃ i : Fin n, affineSegment ℝ (toPlane (v i)) (toPlane (v (finRotate n i))) := rfl
  have hR : (ourPoly hn v).boundary = ⋃ j : ZMod n, (ourPoly hn v).edgeSeg j := rfl
  rw [hL, hR]
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro i
    rw [key i]
    exact Set.subset_iUnion (fun j : ZMod n => (ourPoly hn v).edgeSeg j) (i.val : ZMod n)
  · apply Set.iUnion_subset
    intro j
    refine Set.subset_iUnion_of_subset ⟨j.val, ZMod.val_lt j⟩ ?_
    rw [key ⟨j.val, ZMod.val_lt j⟩]
    rw [show ((⟨j.val, ZMod.val_lt j⟩ : Fin n).val : ZMod n) = j from ZMod.natCast_zmod_val j]

end LeanEval.Geometry.PicksTheorem
