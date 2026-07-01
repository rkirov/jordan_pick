#!/usr/bin/env bash
#
# make_jordan_submission.sh — generate the lean-eval submission workspace for the
# `jordan_curve` problem (https://lean-lang.org/eval/problems/jordan_curve/).
#
# Produces the SOLVER-OWNED parts of the lean-eval workspace:
#   submission/jordan_curve/
#     Submission.lean          -- re-states the eval theorem in the `Submission`
#                                 namespace and delegates to our proof
#     Submission/              -- our (self-contained) Jordan curve development,
#       Root.lean               re-rooted: `JordanPick.JordanCurve` -> `Submission`
#       Arcs.lean  Counting.lean  Brouwer.lean
#     lakefile.toml            -- for local building (lean-eval provides its own,
#     lean-toolchain              along with the trusted Challenge.lean/Solution.lean/config.json)
#
# The proof is self-contained against Mathlib (no Pick-engine dependency, no
# vendored code). To submit: drop `Submission.lean` + `Submission/` into
# lean-eval's `generated/jordan_curve/` workspace (which supplies the trusted
# Challenge.lean/Solution.lean/config.json/lakefile.toml), match its Mathlib pin,
# then `lake exe lean-eval validate-submission --file generated/jordan_curve/Solution.lean`.
#
# Usage:  ./scripts/make_jordan_submission.sh [path-to-repo-root]
#
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
SRC="$ROOT/JordanPick"
OUT="$ROOT/submission/jordan_curve"
LIB="$OUT/Submission"

if [[ ! -f "$SRC/JordanCurve.lean" ]]; then
  echo "ERROR: JCT source not found at $SRC/JordanCurve.lean" >&2
  exit 1
fi

rm -rf "$OUT"
mkdir -p "$LIB"

# Re-root the module prefix `JordanPick.JordanCurve` -> `Submission`.
# (Lean *namespaces* like `JordanCurve`, `JordanCurve.Arcs`, `AddCircle` are
#  independent of module names and are left untouched, so `JordanCurve.jordan_curve`
#  stays accessible from the shim.)
rewrite() { sed -e 's/^import JordanPick\.JordanCurve\./import Submission./' \
                -e 's#JordanPick/JordanCurve#Submission#g' \
                -e 's/JordanPick\.JordanCurve\./Submission./g'; }

# dependency modules -> Submission/<X>.lean
for f in Arcs Counting Brouwer; do
  rewrite < "$SRC/JordanCurve/$f.lean" > "$LIB/$f.lean"
done
# root module JordanCurve.lean -> Submission/Root.lean
rewrite < "$SRC/JordanCurve.lean" > "$LIB/Root.lean"

# The Submission.lean shim: re-state the benchmark theorem in the `Submission`
# namespace (matching Challenge.lean exactly) and delegate to the proven theorem.
cat > "$OUT/Submission.lean" <<'SHIM'
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

theorem jordan_curve
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Function.Injective r) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2 :=
  _root_.JordanCurve.jordan_curve r _hcont _hinj

end Submission
SHIM

# Match the main project's toolchain + Mathlib pin (kept in sync with lean-eval).
cp "$ROOT/lean-toolchain" "$OUT/lean-toolchain"
MREV="$(sed -n 's/^rev = "\(.*\)"/\1/p' "$ROOT/lakefile.toml" | head -1)"
cat > "$OUT/lakefile.toml" <<LAKE
# For local building of the submission library only. In the real lean-eval
# workspace this file is TRUSTED and supplied by the harness (do not edit there).
name = "jordan_curve"
defaultTargets = ["Submission"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "$MREV"

[[lean_lib]]
name = "Submission"
LAKE

echo "Generated $OUT  ($(find "$LIB" -name '*.lean' | wc -l) library files + Submission.lean)"
echo "Solver-owned: Submission.lean + Submission/ (drop into lean-eval generated/jordan_curve/)."
