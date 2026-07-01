import JordanPick.PicksTheorem.Pick.Reductions

/-!
# Pick's theorem: spanning-edge core

Core spanning-edge definitions at a generic height (`vside`, `edgeSign`, `edgeThr`,
`spanningSet`) together with the three spanning-sum facts consumed downstream by the
ear-clipping route: `sum_edgeSign_spanning_eq_zero`, `edgeSign_eq_one_or_neg_one`,
`winding_eq_sum_spanning`.

(The earlier `AlternationCore` / running-sum alternation machinery — an abandoned
route to the `winding ∈ {0,1}` dichotomy, superseded by ear-clipping — has been
removed; only the definitions and spanning-sum lemmas that the live route uses
remain.)
-/

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

/-- `edgeSign` is always `±1` (it is defined by a single `if`). -/
lemma edgeSign_eq_one_or_neg_one (y : ℝ) (i : ZMod P.n) :
    P.edgeSign y i = 1 ∨ P.edgeSign y i = -1 := by
  unfold edgeSign; split_ifs <;> simp

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
    simp only [hsp, hx, and_true, and_false, if_true, if_false,
      mul_one, mul_zero]

end Pick
