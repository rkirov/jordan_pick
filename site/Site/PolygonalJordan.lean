import VersoManual
import Site.Figures

open Verso.Genre Manual

#doc (Manual) "The polygonal Jordan curve theorem" =>

The **polygonal Jordan curve theorem** states that the complement of a simple
polygon's boundary has at most two connected components, with the winding number
locally constant and valued in `{0, 1}`. This is the discrete, combinatorial heart
that powers the Pick development.

`Pick.LatticePolygon.compl_boundary_atMost_two` — `JordanPick/PicksTheorem/Pick.lean`:

```
theorem compl_boundary_atMost_two (P : LatticePolygon) (hS : P.IsSimple) :
    ∃ A B : Set (ℝ × ℝ),
      A ∪ B = P.boundaryᶜ ∧ IsPreconnected A ∧ IsPreconnected B
```

# Approach

The argument is entirely winding-number based. Around the boundary a *tube* is
covered by a left region and a right region, each path-connected and disjoint from
the boundary; the winding number is locally constant on the complement and jumps by
exactly one across an edge, pinning the number of components at two and their
winding values at `0` (outside) and `1` (inside). No general point-set topology of
the Jordan curve theorem is invoked — the separation is proved directly from the
integer per-edge crossing data.

The tube around the boundary is covered by a **left region** (blue) and a
**right region** (red) running along each edge, glued around each vertex by two
**sector caps**. The corner-meet lemmas exhibit an explicit witness
`q = v + ρ·dir θ` in each overlap, making the left and right sides
path-connected all the way around the loop:

```diagram (cssWidth := "26em")
Site.Figures.tubeFigure
```

Simplicity forces the crossings along any horizontal ray to *alternate* in
sign — the boundary is a single loop, so it cannot return to the same side of
the ray without crossing back. Far away the winding is `0`; alternation then
pins it to `{0, 1}` everywhere:

```diagram (cssWidth := "26em")
Site.Figures.alternationFigure
```
