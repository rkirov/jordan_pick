import VersoManual

open Verso.Genre Manual

#doc (Manual) "The Brouwer fixed point theorem" =>

The **Brouwer fixed point theorem** (in dimension two) states that every continuous
self-map of a nonempty compact convex subset of `ℝ²` has a fixed point. It is the
engine under Maehara's proof of the continuous Jordan curve theorem.

`JordanCurve.Brouwer.brouwerFPT` — `JordanPick/JordanCurve/Brouwer.lean`:

```
theorem brouwerFPT : ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x
```

# Approach

The whole chain is original to this repository and self-contained against Mathlib:

* `π₁(S¹) ≅ ℤ` — more precisely, a once-around loop of the circle is not
  null-homotopic. This is the one non-trivial topological input, and it is obtained
  directly from Mathlib's covering-space path lifting
  (`AddCircle.isCoveringMap_coe` together with
  `liftPath_apply_one_eq_of_homotopicRel`), so no external fundamental-group
  development is needed.
* No retraction of the disk onto its boundary (from the circle non-nullhomotopy).
* Brouwer on the disk, via a ray-retraction argument.
* The general convex-compact case, via nearest-point projection.
