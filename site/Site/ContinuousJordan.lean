import VersoManual
import Site.Figures

open Verso.Genre Manual

#doc (Manual) "The continuous Jordan curve theorem" =>

The full **(continuous) Jordan curve theorem** says that a continuous injection of
the circle `S¹` into the plane `ℝ²` has a complement with *exactly* two connected
components. This solves the
[lean-eval jordan curve problem](https://lean-lang.org/eval/problems/jordan_curve/).

`JordanCurve.jordan_curve` — `JordanPick/JordanCurve.lean`:

```
theorem jordan_curve
    (r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2
```

# Approach: Maehara → Brouwer

This is a wholly separate development from the polygonal theorem — it does *not*
use it. It follows **Maehara's proof**, which reduces the separation statement to
the **Brouwer fixed point theorem**. The two supporting lemmas are a crossing lemma
for transversal paths in a rectangle, and the fact that each component has the curve
as its boundary. A farthest-pair normalization and the `l, m, p, q, z₀`
construction then pin down exactly one bounded component, giving the count of two.

After normalizing the farthest pair to `a = (−1,0)`, `b = (1,0)`, the curve
splits into two arcs `Jₙ` (blue) and `Jₛ` (red) inside the rectangle
`[−1,1] × [−2,2]`. The vertical axis meets them at the labelled points, and the
midpoint `z₀` of `p` and `m` lies off the curve. If its component were
unbounded, an escaping path would exit the rectangle at some `w`, and the green
concatenation `s → w → z₀ → m → l → n` would join the bottom wall to the top
wall while *missing* `Jₛ` — contradicting the crossing lemma:

```diagram (cssWidth := "24em")
Site.Figures.maeharaFigure
```

The **crossing lemma** — two continuous paths crossing the rectangle
transversally must meet — is exactly where Brouwer enters:

```diagram (cssWidth := "18em")
Site.Figures.crossingFigure
```

The Brouwer chain underneath is built from the ground up against Mathlib (see the
Brouwer fixed point theorem page).
