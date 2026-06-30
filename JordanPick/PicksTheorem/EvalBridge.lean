import JordanPick.PicksTheorem.Pick

/-!
# Bridge to the lean-lang.org eval Pick problem — base definitions

Reproduces the **exact** trusted helper definitions of the `lean-eval` Pick
problem (`LeanEval/Geometry/PicksTheorem.lean`) and the `ourPoly` reindexing
into our `Pick.LatticePolygon`.  The three bridge obligations live in
`EvalBridgeBoundary`, `EvalBridgeInside`, and are assembled in `EvalBridgeMain`.

See `submission/README.md` for the overall plan.
-/

namespace LeanEval.Geometry.PicksTheorem

open MeasureTheory

/-! ## Trusted eval helper definitions (verbatim — DO NOT EDIT) -/

/-- Coordinatewise cast of a lattice point to the plane. -/
def toPlane (z : ℤ × ℤ) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

/-- The lattice polygon on integer vertex data `v`. -/
def latPoly {n : ℕ} (v : Fin n → ℤ × ℤ) : Polygon (ℝ × ℝ) n :=
  ⟨fun i => toPlane (v i)⟩

/-- The open interior region of a planar curve `S`: points off `S` whose
component in `Sᶜ` is bounded (the Jordan interior for a simple closed curve). -/
def inside (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

/-- Enclosed area: Lebesgue measure of the interior region. -/
noncomputable def area (S : Set (ℝ × ℝ)) : ℝ := (volume (inside S)).toReal

/-- Cyclic adjacency of edge indices. -/
def Adjacent {n : ℕ} (i j : Fin n) : Prop :=
  finRotate n i = j ∨ finRotate n j = i

/-- A simple (Jordan) polygon. -/
def IsSimple {n : ℕ} (poly : Polygon (ℝ × ℝ) n) : Prop :=
  poly.HasNondegenerateEdges ∧
  (∀ i j : Fin n, i ≠ j → ¬ Adjacent i j →
      Disjoint (poly.edgeSet ℝ i) (poly.edgeSet ℝ j)) ∧
  (∀ i : Fin n, poly.edgeSet ℝ i ∩ poly.edgeSet ℝ (finRotate n i)
      = {poly (finRotate n i)})

/-- Number of boundary lattice points. -/
noncomputable def boundaryPts {n : ℕ} (v : Fin n → ℤ × ℤ) : ℕ :=
  Nat.card {z : ℤ × ℤ | toPlane z ∈ (latPoly v).boundary (R := ℝ)}

/-- Number of interior lattice points. -/
noncomputable def interiorPts {n : ℕ} (v : Fin n → ℤ × ℤ) : ℕ :=
  Nat.card {z : ℤ × ℤ | toPlane z ∈ inside ((latPoly v).boundary (R := ℝ))}

/-! ## The reindexing into `Pick.LatticePolygon` -/

/-- Our `LatticePolygon` on the same integer vertex data, reindexed `ZMod n`. -/
def ourPoly {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ) : Pick.LatticePolygon :=
  haveI : NeZero n := ⟨hn.ne'⟩
  { n := n, pos := hn, vert := fun i => v ⟨i.val, ZMod.val_lt i⟩ }

@[simp] theorem ourPoly_n {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ) :
    (ourPoly hn v).n = n := rfl

theorem ourPoly_vert {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ)
    (i : ZMod (ourPoly hn v).n) :
    haveI : NeZero n := ⟨hn.ne'⟩
    (ourPoly hn v).vert i = v ⟨i.val, ZMod.val_lt i⟩ := rfl

end LeanEval.Geometry.PicksTheorem
