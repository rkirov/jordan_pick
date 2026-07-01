import ChallengeDeps
import Submission.EvalBridgeMain

/-!
# lean-eval `pick` — solver submission

The full, self-contained proof lives in the re-rooted development under
`Submission/` (the import-closure of `Submission.EvalBridgeMain`, which is our
`JordanPick.PicksTheorem.EvalBridgeMain`). The 8 trusted helper definitions
(`toPlane`, `latPoly`, `inside`, `area`, `Adjacent`, `IsSimple`, `boundaryPts`,
`interiorPts`) come from the trusted `ChallengeDeps`; our bundle references them
through the `LeanEval.Geometry.PicksTheorem` namespace. Here we restate the
benchmark theorem in the `Submission` namespace and delegate to our proof. It is
axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) and depends only on
Mathlib.
-/

namespace Submission

open LeanEval.Geometry.PicksTheorem MeasureTheory

-- Statement copied verbatim from `Challenge.lean`; only the proof is replaced
-- with a delegation to our development.
theorem pick {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℤ × ℤ) (hsimple : IsSimple (latPoly v)) :
    area ((latPoly v).boundary (R := ℝ))
      = (interiorPts v : ℝ) + (boundaryPts v : ℝ) / 2 - 1 :=
  LeanEval.Geometry.PicksTheorem.pick hn v hsimple

end Submission
