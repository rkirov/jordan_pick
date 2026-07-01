import Submission.Root

/-!
# lean-eval `jordan_curve` — solver submission

The full, self-contained proof lives in the re-rooted development under
`Submission/` (`Submission.Root` is our `JordanCurve` module). Here we restate
the benchmark theorem in the `Submission` namespace and delegate to it. The proof
is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) and depends only on
Mathlib.
-/

namespace Submission

-- Statement copied verbatim from the generated `Submission.lean` stub / `Challenge.lean`;
-- only the proof (`sorry`) is replaced with a delegation to our development.
theorem jordan_curve (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Function.Injective r) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) =
      2 :=
  _root_.JordanCurve.jordan_curve r _hcont _hinj

end Submission
