import Mathlib

/-!
# Pick's theorem — definitions and statement (clean-room)

Freek list #92. Target:
`area P = I + B/2 - 1` for a simple, positively-oriented lattice polygon,
where `area` is the Lebesgue measure of the enclosed region, `I` the number of
interior lattice points, `B` the number of boundary lattice points.

## Design: the winding number is the spine

For a point `q` not on the polygon, `winding P q : ℤ` is computed by signed
ray-crossings — a per-edge integer sum, no transcendental angles. Everything
hangs off it:

* `interiorRegion P := {q | winding P q = 1}` (Jordan interior, for positive
  orientation);
* `area P := volume (interiorRegion P)`;
* the lattice count side is `∑_{q ∈ ℤ²} winding P q`.

The proof chain (each step a separate lemma, all `sorry` for now):
`area = shoelace`  (Green) ;  `shoelace = ∑_q winding`  (core identity) ;
`∑_q winding = I + B/2 - 1`  (polygonal Jordan + Hopf turning number).
-/

namespace Pick

open scoped BigOperators
open MeasureTheory

/-- A lattice point. -/
abbrev Pt := ℤ × ℤ

/-- Embedding of a lattice point into the real plane. -/
def toReal (p : Pt) : ℝ × ℝ := (p.1, p.2)

/-- The 2D cross product `u × v = u₁ v₂ - u₂ v₁` (signed area of the
parallelogram; positive iff `v` is counterclockwise from `u`). -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- A closed lattice polygon: `n` vertices indexed cyclically by `ZMod n`.
Edge `i` runs from `vert i` to `vert (i+1)`, with `i+1` taken mod `n`, so the
curve is automatically closed. -/
structure LatticePolygon where
  n : ℕ
  pos : 0 < n
  vert : ZMod n → Pt

namespace LatticePolygon

variable (P : LatticePolygon)

instance : NeZero P.n := ⟨P.pos.ne'⟩

/-- The (real) closed segment that is edge `i`. -/
def edgeSeg (i : ZMod P.n) : Set (ℝ × ℝ) :=
  segment ℝ (toReal (P.vert i)) (toReal (P.vert (i + 1)))

/-- The boundary curve: the union of all edges. -/
def boundary : Set (ℝ × ℝ) := ⋃ i, P.edgeSeg i

/-- Contribution of the directed edge `a → b` to the winding number around `q`,
via the standard signed ray-crossing rule. -/
noncomputable def edgeWind (a b q : ℝ × ℝ) : ℤ :=
  if a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a) then 1
  else if b.2 ≤ q.2 ∧ q.2 < a.2 ∧ cross (b - a) (q - a) < 0 then -1
  else 0

/-- The winding number of the polygon around a point `q` (not on the boundary):
the signed number of times the polygon wraps around `q`. -/
noncomputable def winding (q : ℝ × ℝ) : ℤ :=
  ∑ i, edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) q

/-- The enclosed region (Jordan interior, for a positively-oriented polygon):
the points the curve winds around exactly once. -/
def interiorRegion : Set (ℝ × ℝ) := {q | P.winding q = 1}

/-- The enclosed area: Lebesgue measure of the interior region, as a real. -/
noncomputable def area : ℝ := (volume P.interiorRegion).toReal

/-- The interior lattice points: lattice points strictly inside. -/
def interiorLattice : Set Pt := {q | P.winding (toReal q) = 1 ∧ toReal q ∉ P.boundary}

/-- The boundary lattice points: lattice points lying on some edge. -/
def boundaryLattice : Set Pt := {q | toReal q ∈ P.boundary}

/-- `I`: number of interior lattice points. -/
noncomputable def I : ℕ := P.interiorLattice.ncard

/-- `B`: number of boundary lattice points. -/
noncomputable def B : ℕ := P.boundaryLattice.ncard

/-- The shoelace (signed) area: `½ ∑ (xᵢ yᵢ₊₁ − xᵢ₊₁ yᵢ)`. -/
noncomputable def shoelace : ℝ :=
  (∑ i, cross (toReal (P.vert i)) (toReal (P.vert (i + 1)))) / 2

/-- The polygon is **simple**: distinct edges meet only at shared vertices.
Three clauses (matching the `lean-eval` `IsSimple`): no degenerate edge;
non-adjacent edges are disjoint; consecutive (adjacent) edges meet **exactly** at
their shared vertex. The third clause is what makes the boundary a genuine Jordan
curve (rules out collinear backtracking) and gives distinct ray-crossings for the
two adjacent spanning edges of a triangle. -/
def IsSimple : Prop :=
  (∀ i, P.vert i ≠ P.vert (i + 1)) ∧
    (∀ i j, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → Disjoint (P.edgeSeg i) (P.edgeSeg j)) ∧
    (∀ i, P.edgeSeg i ∩ P.edgeSeg (i + 1) = {toReal (P.vert (i + 1))})

/-- The polygon is **positively oriented** (counterclockwise): its signed area
is positive. -/
def PositivelyOriented : Prop := 0 < P.shoelace

end LatticePolygon

open LatticePolygon

/-- **Pick's theorem** (Freek #92): the area of a simple, positively-oriented
lattice polygon equals `I + B/2 − 1`. -/
theorem pick (P : LatticePolygon) (hsimple : P.IsSimple)
    (horient : P.PositivelyOriented) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 := by
  sorry

end Pick
