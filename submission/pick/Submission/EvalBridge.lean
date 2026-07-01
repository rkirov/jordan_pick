import Submission.Pick
import ChallengeDeps

/-!
# Bridge to the lean-lang.org eval Pick problem — base definitions

Reproduces the **exact** trusted helper definitions of the `lean-eval` Pick
problem (`LeanEval/Geometry/PicksTheorem.lean`) and the `ourPoly` reindexing
into our `Pick.LatticePolygon`.  The three bridge obligations live in
`EvalBridgeBoundary`, `EvalBridgeInside`, and are assembled in `EvalBridgeMain`.

See `submission/README.md` for the overall plan.
-/

namespace LeanEval.Geometry.PicksTheorem

open MeasureTheory

/-! ## Trusted eval helper definitions

The 8 trusted helpers (`toPlane`, `latPoly`, `inside`, `area`, `Adjacent`,
`IsSimple`, `boundaryPts`, `interiorPts`) are NOT redefined here — they come
from `ChallengeDeps` (imported above). Our development originally defined a
byte-identical copy; in the submission bundle they resolve, through the open
namespace `LeanEval.Geometry.PicksTheorem`, to the trusted `ChallengeDeps`
versions. -/

/-! ## The reindexing into `Pick.LatticePolygon` -/

/-- Our `LatticePolygon` on the same integer vertex data, reindexed `ZMod n`. -/
def ourPoly {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ) : Pick.LatticePolygon :=
  haveI : NeZero n := ⟨hn.ne'⟩
  { n := n, pos := hn, vert := fun i => v ⟨i.val, ZMod.val_lt i⟩ }

@[simp] theorem ourPoly_n {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ) :
    (ourPoly hn v).n = n := rfl

theorem ourPoly_vert {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ × ℤ)
    (i : ZMod (ourPoly hn v).n) :
    haveI : NeZero n := ⟨hn.ne'⟩
    (ourPoly hn v).vert i = v ⟨i.val, ZMod.val_lt i⟩ := rfl

end LeanEval.Geometry.PicksTheorem
