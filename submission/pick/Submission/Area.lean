import Submission.Defs

/-!
# Algebra of `cross`

Basic bilinear/alternating identities for `Pick.cross`, used by the per-edge
weight identity and the `area = shoelace` step.
-/

namespace Pick

variable (u v w : ℝ × ℝ)

@[simp] lemma cross_self : cross u u = 0 := by unfold cross; ring

lemma cross_skew : cross u v = - cross v u := by unfold cross; ring

@[simp] lemma toReal_add (p c : Pt) : toReal (p + c) = toReal p + toReal c := by
  unfold toReal
  simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Int.cast_add]

/-- Signed area of the trapezoid under the directed edge `u → v` (down to the
`x`-axis). Summed cyclically over a polygon's edges this gives the shoelace area;
per edge it is the target of the lattice-point weight identity (Step 1). -/
noncomputable def trapezoidArea (u v : ℝ × ℝ) : ℝ := (u.1 - v.1) * (u.2 + v.2) / 2

/-- `trapezoidArea` of a lattice edge as an explicit integer expression cast to
`ℝ`: `½ (u.1−v.1)(u.2+v.2)`. This is the form the lattice-point count produces,
used to match the count side to the area side in the per-edge identity. -/
lemma trapezoidArea_toReal (u v : Pt) :
    trapezoidArea (toReal u) (toReal v)
      = (((u.1 - v.1) * (u.2 + v.2) : ℤ) : ℝ) / 2 := by
  unfold trapezoidArea toReal
  dsimp only
  push_cast
  ring

/-- The rational value the lattice-point count produces,
`−½ (u.2+v.2)(v.1−u.1)`, cast to `ℝ`, equals `trapezoidArea`. This bridges the
`ℚ`-valued count side to the `ℝ`-valued area side in the per-edge identity. -/
lemma count_value_eq_trapezoid (u v : Pt) :
    ((-(u.2 + v.2) * (v.1 - u.1) / 2 : ℚ) : ℝ) = trapezoidArea (toReal u) (toReal v) := by
  rw [trapezoidArea_toReal]
  push_cast
  ring

/-- The cyclic sum of per-edge trapezoid areas equals the shoelace area: the
`u.1*u.2` corner terms telescope away, leaving `½ ∑ cross`. -/
theorem sum_trapezoidArea_eq_shoelace (P : LatticePolygon) :
    (∑ i, trapezoidArea (toReal (P.vert i)) (toReal (P.vert (i + 1)))) = P.shoelace := by
  have key : ∀ i, trapezoidArea (toReal (P.vert i)) (toReal (P.vert (i + 1)))
      = cross (toReal (P.vert i)) (toReal (P.vert (i + 1))) / 2
        + ((toReal (P.vert i)).1 * (toReal (P.vert i)).2
           - (toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2) / 2 := by
    intro i; unfold trapezoidArea cross; ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  have tele : (∑ i, ((toReal (P.vert i)).1 * (toReal (P.vert i)).2
      - (toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2) / 2) = 0 := by
    have reindex : (∑ i, (toReal (P.vert (i + 1))).1 * (toReal (P.vert (i + 1))).2)
        = ∑ i, (toReal (P.vert i)).1 * (toReal (P.vert i)).2 :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod P.n))
        (fun i => (toReal (P.vert i)).1 * (toReal (P.vert i)).2)
    rw [← Finset.sum_div, Finset.sum_sub_distrib, reindex, sub_self, zero_div]
  rw [tele, add_zero]
  unfold LatticePolygon.shoelace
  rw [Finset.sum_div]

end Pick
