import JordanPick.PicksTheorem.EvalBridge

/-!
# Bridge obligation: the Jordan identification (the hard one)

Stated purely about our `ourPoly` (the assembly file combines it with
`boundary_bridge`): the eval topological interior of our polygon's boundary
equals the winding-nonzero set off the boundary.

`inside ((ourPoly hn v).boundary) = {x | x ∉ boundary ∧ winding x ≠ 0}`.

This is the polygonal Jordan curve theorem in the form the eval needs.  It
reuses our `Pick.…compl_boundary_atMost_two` (the complement of the boundary has
≤ 2 connected components, with `winding` locally constant `∈ {0,1}` orientation-
free `{0,v}`) plus:
* `{winding ≠ 0}` is bounded (winding vanishes outside the vertex bounding box),
  so the connected component of any such point is bounded;
* the unbounded component carries `winding = 0` (far-field);
* the interior is nonempty (`shoelace ≠ 0` for a simple polygon), so there is a
  genuine bounded component and it is exactly `{winding ≠ 0}`.

Note the `∉ boundary` conjunct: `inside S ⊆ Sᶜ` by definition, and the winding
*formula* may be nonzero at boundary points, so it must be excluded.
-/

namespace LeanEval.Geometry.PicksTheorem

open MeasureTheory

/-- **Bridge obligation — Jordan identification** (about `ourPoly`). -/
theorem inside_eq {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ)
    (hsimple : (ourPoly hn v).IsSimple) :
    inside ((ourPoly hn v).boundary)
      = {x | x ∉ (ourPoly hn v).boundary ∧ (ourPoly hn v).winding x ≠ 0} := by
  set Q := ourPoly hn v with hQ
  ext x
  simp only [inside, Set.mem_ofPred_eq]
  constructor
  · -- bounded component ⟹ winding ≠ 0
    rintro ⟨hxb, hxbd⟩
    refine ⟨hxb, ?_⟩
    intro h0
    -- if `winding x = 0`, the off-boundary exterior set reaches arbitrarily far,
    -- contradicting boundedness of the component.
    obtain ⟨Rc, hRc⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hxbd
    obtain ⟨S, hSsub, hSpre, hxS, q₀, hq₀S, hq₀far⟩ :=
      Pick.exterior_reaches_far_beyond Q hsimple hxb h0 Rc
    have hScomp : S ⊆ connectedComponentIn Q.boundaryᶜ x :=
      hSpre.subset_connectedComponentIn hxS hSsub
    have hmem := hRc (hScomp hq₀S)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    linarith
  · -- winding ≠ 0 ⟹ component bounded (it lies in the bounded winding support)
    rintro ⟨hxb, hxw⟩
    refine ⟨hxb, ?_⟩
    have hcompsub : connectedComponentIn Q.boundaryᶜ x ⊆ {y : ℝ × ℝ | Q.winding y ≠ 0} := by
      intro y hy
      have hconst : Q.winding y = Q.winding x :=
        Pick.winding_const_on_connectedComponentIn Q hxb hy
      rw [Set.mem_ofPred_eq, hconst]; exact hxw
    exact (Pick.windingSupport_bounded Q).subset hcompsub

end LeanEval.Geometry.PicksTheorem
