import VersoManual
import Site.Figures

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

The running example below has `I = 3` interior points (red), `B = 9` boundary
lattice points (open circles), and area `6½ = 3 + 9/2 − 1`. The dots in this
figure are *computed* by the same ray-casting rule the proof uses:

```diagram (cssWidth := "26em")
Site.Figures.pickStatement
```

# Approach

The spine of the development is the **winding number**, encoded as a per-edge
signed ray-crossing sum — pure integer arithmetic, with no transcendental angles
and no general topology. From it, Green's theorem gives `area = ∫∫ winding =
shoelace`; the polygonal Jordan curve theorem gives `winding ∈ {0, 1}`; and
**ear-clipping induction** (the Meisters two-ears theorem, via a
deepest-contained-vertex diagonal split with a non-circular winding-jump
separation argument) reduces the area identity to the triangle case.

The winding number of a point `q` counts signed crossings of its rightward ray
with the boundary: up-crossings `+1`, down-crossings `−1`. Inside, they sum to
`1`; outside, they cancel to `0`:

```diagram (cssWidth := "26em")
Site.Figures.windingFigure
```

Integrating the winding number over the plane and slicing per edge yields the
signed-trapezoid (shoelace) formula — each edge contributes the trapezoid
between itself and the `x`-axis, positively or negatively according to its
direction:

```diagram (cssWidth := "24em")
Site.Figures.trapezoidFigure
```

The induction that carries the identity from triangles to all simple polygons
clips an *ear* (Meisters): a diagonal at a suitable convex vertex splits the
polygon into a triangle and a smaller polygon, and the winding numbers add:

```diagram (cssWidth := "24em")
Site.Figures.earClipFigure
```

A separate **lean-eval** target (<https://lean-lang.org/eval/problems/pick/>)
bridges this to Mathlib's `Polygon` with the *topological* interior and no
orientation hypothesis: `LeanEval.Geometry.PicksTheorem.pick` in
`JordanPick/PicksTheorem/EvalBridgeMain.lean`.

The lattice-count side (`latWeight` / `latWeightSum`) follows the discrete
angle-weight device of Eisermann, with the per-edge identity proved
independently here by a column decomposition; the geometric core (the polygonal
Jordan curve theorem and the ear-clipping reduction) is original.

The angle weight assigns each lattice point the fraction of a small disk around
it that lies inside the polygon — `1` for interior points, `½` for edge points,
`θ/2π` at a vertex of interior angle `θ` — and `latWeightSum` totals it per
edge:

```diagram (cssWidth := "30em")
Site.Figures.weightFigure
```
