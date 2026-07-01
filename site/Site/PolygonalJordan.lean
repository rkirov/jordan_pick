import VersoManual

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
