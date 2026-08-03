import VersoManual
import Site.Pick
import Site.PolygonalJordan
import Site.ContinuousJordan
import Site.Brouwer

open Verso.Genre Manual

#doc (Manual) "jordan\\_pick" =>

A clean-room Lean 4 / Mathlib formalization of **Pick's theorem** (Freek's
*Formalizing 100 Theorems* #92), the **polygonal Jordan curve theorem**, and the
full **(continuous) Jordan curve theorem** — all genuinely missing from Mathlib.
Two lean-eval problems are solved:
[`pick`](https://lean-lang.org/eval/problems/pick/) and
[`jordan_curve`](https://lean-lang.org/eval/problems/jordan_curve/).

Every result is proved **sorry-free**; `#print axioms` shows only the three standard
axioms `[propext, Classical.choice, Quot.sound]`. The project is pinned to Lean
`v4.32.2` + Mathlib `905b9581` to match the lean-eval harness.

[Source repository](https://github.com/rkirov/jordan-pick) · the four headline
results are each documented below, with the exact Lean statement shown verbatim.

# Main results

* **Pick's theorem** — `Pick.pick`: a simple, positively-oriented lattice polygon
  has `area = I + B/2 − 1`.
* **Polygonal Jordan curve theorem** — `Pick.LatticePolygon.compl_boundary_atMost_two`:
  the complement of a simple polygon's boundary has at most two connected
  components.
* **Continuous Jordan curve theorem** — `JordanCurve.jordan_curve`: a continuous
  injection `S¹ → ℝ²` has a complement with exactly two components.
* **Brouwer fixed point theorem (2D)** — `JordanCurve.Brouwer.brouwerFPT`: every
  continuous self-map of a nonempty compact convex subset of `ℝ²` has a fixed
  point.

{include 0 Site.Pick}

{include 0 Site.PolygonalJordan}

{include 0 Site.ContinuousJordan}

{include 0 Site.Brouwer}
