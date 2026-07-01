import VersoManual

open Verso.Genre Manual

#doc (Manual) "Pick's theorem" =>

**Pick's theorem** (Freek's *Formalizing 100 Theorems* #92) relates the area of a
simple lattice polygon to the lattice points it touches: if `I` is the number of
interior lattice points and `B` the number of boundary lattice points, then the
area is `I + B/2 − 1`.

The formalization here proves the identity for a simple, positively-oriented
lattice polygon, where *area* is the rigorous Lebesgue measure of the enclosed
region (the winding interior) — not shoelace-as-definition.

`Pick.pick` — `JordanPick/PicksTheorem/Pick.lean`:

```
theorem pick (P : LatticePolygon) (hS : P.IsSimple) (hO : P.PositivelyOriented) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1
```

# Approach

The spine of the development is the **winding number**, encoded as a per-edge
signed ray-crossing sum — pure integer arithmetic, with no transcendental angles
and no general topology. From it, Green's theorem gives `area = ∫∫ winding =
shoelace`; the polygonal Jordan curve theorem gives `winding ∈ {0, 1}`; and
**ear-clipping induction** (the Meisters two-ears theorem, via a
deepest-contained-vertex diagonal split with a non-circular winding-jump
separation argument) reduces the area identity to the triangle case.

A separate **lean-eval** target (<https://lean-lang.org/eval/problems/pick/>)
bridges this to Mathlib's `Polygon` with the *topological* interior and no
orientation hypothesis: `LeanEval.Geometry.PicksTheorem.pick` in
`JordanPick/PicksTheorem/EvalBridgeMain.lean`.

The lattice-count side (`latWeight` / `latWeightSum`) follows the discrete
angle-weight device of Eisermann & Zumkeller, with the per-edge identity proved
independently here by a column decomposition; the geometric core (the polygonal
Jordan curve theorem and the ear-clipping reduction) is original.
