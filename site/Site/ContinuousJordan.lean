import VersoManual

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

The Brouwer chain underneath is built from the ground up against Mathlib (see the
Brouwer fixed point theorem page).
