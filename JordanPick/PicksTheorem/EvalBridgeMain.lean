import JordanPick.PicksTheorem.EvalBridgeBoundary
import JordanPick.PicksTheorem.EvalBridgeInside
import JordanPick.PicksTheorem.EvalBridgeSimple
import JordanPick.PicksTheorem.EvalBridgeReverse

/-!
# Bridge assembly: the eval `pick` from `Pick.pick`

`eval_bridge` packages the obligations into a positively-oriented representative;
`pick` is then immediate.

`eval_bridge` still needs, beyond `boundary_bridge`/`inside_bridge`:
* eval `IsSimple (latPoly v) → (ourPoly hn v).IsSimple`;
* the orientation WLOG — `(ourPoly hn v).shoelace ≠ 0` for a simple polygon
  (`Pick.…shoelace_ne_zero_of_isSimple`); take the polygon itself if
  `shoelace > 0`, else its reverse, which is positively oriented, has the same
  boundary, the same `inside`, and the same lattice counts;
* `interiorPts v = Q.I` and `boundaryPts v = Q.B` (`Nat.card = Set.ncard` on the
  finite lattice sets, via `inside_bridge`/`boundary_bridge`).
-/

namespace LeanEval.Geometry.PicksTheorem

open MeasureTheory

/-- **Bridge obligation — packaged.** -/
theorem eval_bridge {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    ∃ Q : Pick.LatticePolygon, Q.IsSimple ∧ Q.PositivelyOriented ∧
      area ((latPoly v).boundary (R := ℝ)) = Q.area ∧
      interiorPts v = Q.I ∧ boundaryPts v = Q.B := by
  have hn0 : 0 < n := by omega
  set P := ourPoly hn0 v with hPdef
  have hP : P.IsSimple := ourPoly_isSimple hn0 v hsimple
  have hne : P.shoelace ≠ 0 := Pick.shoelace_ne_zero_of_isSimple P hP
  have hbnull : P.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact Pick.volume_boundary_eq_zero P hP
  -- Uniform packaging of any positively-oriented representative `Q` with the same
  -- boundary and the off-boundary identification `Q.winding = 1 ↔ P.winding ≠ 0`.
  have key : ∀ Q : Pick.LatticePolygon, Q.IsSimple → Q.PositivelyOriented →
      Q.boundary = P.boundary →
      (∀ x, x ∉ P.boundary → (Q.winding x = 1 ↔ P.winding x ≠ 0)) →
      Q.IsSimple ∧ Q.PositivelyOriented ∧
        area ((latPoly v).boundary (R := ℝ)) = Q.area ∧
        interiorPts v = Q.I ∧ boundaryPts v = Q.B := by
    intro Q hsQ hposQ hbdry hwind
    refine ⟨hsQ, hposQ, ?_, ?_, ?_⟩
    · -- area
      simp only [area, Pick.LatticePolygon.area, Pick.LatticePolygon.interiorRegion]
      rw [boundary_bridge hn0 v, inside_eq hn0 v hP, ← hPdef]
      congr 1
      apply MeasureTheory.measure_congr
      filter_upwards [hbnull] with x hx
      have hxb : x ∉ P.boundary := hx
      apply propext
      constructor
      · rintro ⟨_, hw⟩; exact (hwind x hxb).mpr hw
      · intro ht; exact ⟨hxb, (hwind x hxb).mp ht⟩
    · -- interiorPts
      have hset : {z : ℤ × ℤ | toPlane z ∈ {x | x ∉ P.boundary ∧ P.winding x ≠ 0}}
          = Q.interiorLattice := by
        ext z
        simp only [Set.mem_ofPred_eq, Pick.LatticePolygon.interiorLattice]
        constructor
        · rintro ⟨hb, hw⟩
          exact ⟨(hwind (Pick.toReal z) hb).mpr hw, by rw [hbdry]; exact hb⟩
        · rintro ⟨h1, hb⟩
          have hbP : Pick.toReal z ∉ P.boundary := by rw [← hbdry]; exact hb
          exact ⟨hbP, (hwind (Pick.toReal z) hbP).mp h1⟩
      unfold interiorPts
      simp only [Pick.LatticePolygon.I]
      rw [boundary_bridge hn0 v, inside_eq hn0 v hP, ← hPdef, Nat.card_coe_set_eq, hset]
    · -- boundaryPts
      have hset : {z : ℤ × ℤ | toPlane z ∈ P.boundary} = Q.boundaryLattice := by
        ext z
        simp only [Set.mem_ofPred_eq, Pick.LatticePolygon.boundaryLattice, hbdry,
          toPlane, Pick.toReal]
      unfold boundaryPts
      simp only [Pick.LatticePolygon.B]
      rw [boundary_bridge hn0 v, ← hPdef, Nat.card_coe_set_eq, hset]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `shoelace < 0`: take the reverse, which is positively oriented.
    have hsQ : (Pick.reverseP P).IsSimple := Pick.LatticePolygon.reverseP_isSimple P hP
    have hposQ : (Pick.reverseP P).PositivelyOriented := by
      show 0 < (Pick.reverseP P).shoelace
      rw [Pick.reverseP_shoelace]; linarith
    have hbQ : (Pick.reverseP P).boundary = P.boundary :=
      Pick.LatticePolygon.reverseP_boundary P
    refine ⟨Pick.reverseP P, key (Pick.reverseP P) hsQ hposQ hbQ ?_⟩
    intro x hx
    have hxQ : x ∉ (Pick.reverseP P).boundary := by rw [hbQ]; exact hx
    have h01 := Pick.winding_zero_or_one (Pick.reverseP P) hsQ hposQ x hxQ
    rw [Pick.LatticePolygon.reverseP_winding] at h01 ⊢
    omega
  · -- `shoelace > 0`: take `P` itself.
    refine ⟨P, key P hP hpos rfl ?_⟩
    intro x hx
    have h01 := Pick.winding_zero_or_one P hP hpos x hx
    omega

/-- **Pick's theorem** (eval statement), reduced to our `Pick.pick`. -/
theorem pick {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    area ((latPoly v).boundary (R := ℝ))
      = (interiorPts v : ℝ) + (boundaryPts v : ℝ) / 2 - 1 := by
  obtain ⟨Q, hsimp, hpos, harea, hI, hB⟩ := eval_bridge hn v hsimple
  rw [harea, hI, hB]
  exact Pick.pick Q hsimp hpos

end LeanEval.Geometry.PicksTheorem
