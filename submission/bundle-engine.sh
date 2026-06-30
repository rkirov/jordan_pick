#!/usr/bin/env bash
#
# bundle-engine.sh — bundle the JordanPick Pick engine into a self-contained
# lean-eval submission tree.
#
# The lean-eval submission must compile against Mathlib ONLY (it cannot
# `import JordanPick`). This script copies our proof engine into
# `Submission/Engine/` and rewrites the internal module prefix
# `JordanPick.PicksTheorem` -> `Submission.Engine`, so the bundled copy is
# self-contained. It also copies the bridge to `Submission/Bridge.lean`.
#
# Usage:  ./bundle-engine.sh /path/to/jordan_pick
#   (defaults to ../  i.e. the parent of this submission/ dir)
#
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
SRC="$ROOT/JordanPick/PicksTheorem"
OUT="$(cd "$(dirname "$0")" && pwd)/Submission"
ENGINE="$OUT/Engine"

if [[ ! -d "$SRC" ]]; then
  echo "ERROR: engine source not found at $SRC" >&2
  exit 1
fi

rm -rf "$ENGINE"
mkdir -p "$ENGINE/Pick"

rewrite() { sed -e 's/JordanPick\.PicksTheorem/Submission.Engine/g' \
                -e 's#JordanPick/PicksTheorem#Submission/Engine#g'; }

# top-level engine modules (dependency order is irrelevant — imports carry it)
for f in Defs Winding Area Weight PerEdge Jordan Pick; do
  rewrite < "$SRC/$f.lean" > "$ENGINE/$f.lean"
done
# the Pick/ subpackage
for f in Reductions Alternation Corners BoundaryArcs Slab Routing EarClip; do
  rewrite < "$SRC/Pick/$f.lean" > "$ENGINE/Pick/$f.lean"
done

# the bridge modules (proved, sorry-free): base defs + 4 obligations + assembly.
# They live alongside the engine so their `Submission.Engine.…` imports resolve.
for f in EvalBridge EvalBridgeBoundary EvalBridgeInside EvalBridgeSimple \
         EvalBridgeReverse EvalBridgeMain; do
  rewrite < "$SRC/$f.lean" > "$ENGINE/$f.lean"
done

echo "Bundled -> $ENGINE  ($(find "$ENGINE" -name '*.lean' | wc -l) files)"
echo
echo "The proved eval theorem is  LeanEval.Geometry.PicksTheorem.pick"
echo "in Submission/Engine/EvalBridgeMain.lean (sorry-free, axiom-clean)."
echo
echo "NOTE: Submission/Engine/EvalBridge.lean *defines* the eval helpers"
echo "(toPlane, latPoly, inside, area, Adjacent, IsSimple, boundaryPts,"
echo "interiorPts) so the tree compiles standalone. In the real submission"
echo "these are TRUSTED (from Challenge.lean, same namespace): delete that"
echo "def block from EvalBridge.lean and import the challenge file instead,"
echo "so there is no duplicate definition (see README.md)."
