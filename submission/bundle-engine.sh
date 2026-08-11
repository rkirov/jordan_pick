#!/usr/bin/env bash
#
# bundle-engine.sh — regenerate the vendored Pick engine inside the lean-eval
# submission workspace from the library in JordanPick/PicksTheorem.
#
# The lean-eval workspace must compile against Mathlib ONLY (it cannot
# `import JordanPick`), so the engine is copied into `submission/pick/Submission/`
# with its module prefix rewritten `JordanPick.PicksTheorem` -> `Submission`.
# Re-run this whenever the library changes, so the workspace never drifts.
#
# Usage:  ./bundle-engine.sh [/path/to/jordan_pick]
#   (defaults to ../  i.e. the parent of this submission/ dir)
#
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="${1:-$(cd "$HERE/.." && pwd)}"
SRC="$ROOT/JordanPick/PicksTheorem"
OUT="$HERE/pick/Submission"

if [[ ! -d "$SRC" ]]; then
  echo "ERROR: engine source not found at $SRC" >&2
  exit 1
fi

rewrite() {
  sed -e 's/JordanPick\.PicksTheorem/Submission/g' \
      -e 's#JordanPick/PicksTheorem#Submission#g'
}

rm -rf "$OUT"
# Mirror the whole library tree; `find` rather than a hardcoded list, so a new
# module added to the library cannot be silently left out of the bundle.
while IFS= read -r f; do
  rel="${f#"$SRC"/}"
  mkdir -p "$OUT/$(dirname "$rel")"
  rewrite < "$f" > "$OUT/$rel"
done < <(find "$SRC" -name '*.lean' | sort)

# The single edit relative to the library: `Submission/EvalBridge.lean` must not
# redefine the 8 trusted helper definitions. In the workspace they come from the
# trusted `ChallengeDeps` module, so that the declarations the Solution is built
# from are identical to the ones `Challenge.lean` states the theorem with.
python3 - "$OUT/EvalBridge.lean" <<'PY'
import re, sys
path = sys.argv[1]
src = open(path, encoding='utf-8').read()

first, rest = src.split('\n', 1)
assert first == 'import Submission.Pick', first
src = first + '\nimport ChallengeDeps\n' + rest

start = '/-! ## Trusted eval helper definitions (verbatim — DO NOT EDIT) -/'
end   = '/-! ## The reindexing into `Pick.LatticePolygon` -/'
i, j = src.index(start), src.index(end)
note = """/-! ## Trusted eval helper definitions

The 8 trusted helpers (`toPlane`, `latPoly`, `inside`, `area`, `Adjacent`,
`IsSimple`, `boundaryPts`, `interiorPts`) are NOT redefined here — they come
from `ChallengeDeps` (imported above). Our development originally defined a
byte-identical copy; in the submission bundle they resolve, through the open
namespace `LeanEval.Geometry.PicksTheorem`, to the trusted `ChallengeDeps`
versions. -/

"""
open(path, 'w', encoding='utf-8').write(src[:i] + note + src[j:])
print(f"patched {path}: dropped the 8 helper defs, added `import ChallengeDeps`")
PY

echo "Bundled -> $OUT  ($(find "$OUT" -name '*.lean' | wc -l) files)"
echo
echo "The proved eval theorem is  LeanEval.Geometry.PicksTheorem.pick"
echo "in Submission/EvalBridgeMain.lean (sorry-free, axiom-clean)."
echo
echo "Note: submission/pick/Challenge.lean deliberately does NOT import"
echo "ChallengeDeps — it inlines those 8 definitions so that its transitive"
echo "import closure is Mathlib-only, as the Palomar registry requires of a"
echo "Challenge module. The definitions are byte-identical to ChallengeDeps."
