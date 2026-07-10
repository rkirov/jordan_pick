#!/usr/bin/env bash
#
# make_rado_submission.sh — generate the lean-eval submission workspace for the
# `rado_riemannSurface` problem (https://lean-lang.org/eval/problems/rado_riemannSurface/).
#
# Produces the SOLVER-OWNED parts of the lean-eval workspace:
#   submission/rado_riemannSurface/
#     Submission.lean          -- re-states the eval theorem in the `Submission`
#                                 namespace and delegates to our proof
#     Submission/              -- the (self-contained) Radó development,
#       Topology/SecondCountable.lean   re-rooted: module prefix `Rado.` -> `Submission.`
#       Topology/PoincareVolterra.lean  (the Lean *namespace* `Rado` inside the files
#       Complex/{SubMean,Poisson,Dirichlet,PlanarConnected}.lean   is untouched)
#       Surface/{Charts,Core}.lean
#       Main.lean
#
# The trusted workspace files (Challenge.lean, Solution.lean, config.json,
# holes.json, WorkspaceTest.lean, README.md, lakefile.toml, lean-toolchain) come
# verbatim from lean-eval's generated/rado_riemannSurface/ (mirrored in
# reference/rado/harness/) and are only seeded here if absent.
#
# To submit: point the lean-eval submission issue at a repo containing this
# directory (lakefile name matches the problem id; CI overlays only
# Submission.lean + Submission/**). Local check: `lake exe cache get && lake build`
# inside the workspace, or lean-eval's `lake test`.
#
# Usage:  ./scripts/make_rado_submission.sh [path-to-repo-root]
#
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
SRC="$ROOT/Rado"
HARNESS="$ROOT/reference/rado/harness"
OUT="$ROOT/submission/rado_riemannSurface"
LIB="$OUT/Submission"

if [[ ! -f "$SRC/Main.lean" ]]; then
  echo "ERROR: Radó source not found at $SRC/Main.lean" >&2
  exit 1
fi

mkdir -p "$OUT"

# Seed the trusted files from the mirrored harness copies if not already there.
seed() { [[ -f "$OUT/$2" ]] || cp "$HARNESS/$1" "$OUT/$2"; }
seed generated_rado_riemannSurface_Challenge.lean Challenge.lean
seed generated_rado_riemannSurface_Solution.lean  Solution.lean
seed generated_rado_riemannSurface_lakefile.toml  lakefile.toml
seed gen_config.json        config.json
seed gen_holes.json         holes.json
seed gen_WorkspaceTest.lean WorkspaceTest.lean
seed gen_README.md          README.md
[[ -f "$OUT/lean-toolchain" ]] || cp "$ROOT/lean-toolchain" "$OUT/lean-toolchain"

# Regenerate the solver-owned parts.
rm -rf "$LIB"
mkdir -p "$LIB/Topology" "$LIB/Complex" "$LIB/Surface"

# Re-root the module prefix `Rado.` -> `Submission.`; Lean namespaces untouched.
rewrite() { sed -e 's/^import Rado\./import Submission./'; }

# NOTE: Rado/Main.lean is deliberately NOT bundled — it declares the theorem at
# root level under the exact eval name, which would collide with the trusted
# Solution.lean in the same workspace. The shim below proves the Submission-
# namespace statement directly from the assembly theorem in Surface/Core.
for f in Topology/SecondCountable Topology/PoincareVolterra \
         Complex/SubMean Complex/Poisson Complex/Dirichlet Complex/PlanarConnected \
         Surface/Charts Surface/Core; do
  rewrite < "$SRC/$f.lean" > "$LIB/$f.lean"
done

# The Submission.lean shim: restate the benchmark theorem in the `Submission`
# namespace (matching Challenge.lean exactly) and delegate to the proven theorem.
cat > "$OUT/Submission.lean" <<'SHIM'
import Submission.Surface.Core

/-!
# lean-eval `rado_riemannSurface` — solver submission

**Radó's theorem**: a connected Hausdorff Riemann surface is second countable.

The full, self-contained proof lives in the re-rooted development under
`Submission/`, culminating in `Rado.secondCountableTopology_of_riemannSurface`
(`Submission/Surface/Core.lean`).
Route: Perron's method on an explicit two-disk configuration (Schwarz/Poisson
solution of the Dirichlet problem, chartwise subharmonic functions, explicit
log-barriers) produces a nonconstant harmonic function; the étale space of its
harmonic-conjugate germs has an evaluation map with discrete fibers; the
Poincaré–Volterra lemma and descent along the open covering projection give
second countability. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`),
depends only on Mathlib.
-/

namespace Submission

-- Statement copied verbatim from Challenge.lean; only the proof is replaced
-- with a delegation to our development.
theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X :=
  Rado.secondCountableTopology_of_riemannSurface

end Submission
SHIM

echo "Regenerated solver-owned parts in $OUT: Submission.lean + Submission/ ($(find "$LIB" -name '*.lean' | wc -l) library files)."
echo "Trusted files seeded from $HARNESS (left untouched if already present)."
