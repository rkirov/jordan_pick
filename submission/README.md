# lean-eval Pick's theorem submission — scaffold

Target: <https://lean-lang.org/eval/problems/pick/>
(source: `leanprover/lean-eval` → `LeanEval/Geometry/PicksTheorem.lean`).

Intended home: the **`jordan_pick`** repo (polygonal Jordan curve theorem +
Pick's theorem). The polygonal JCT is the engine underneath Pick, so both live
together naturally.

---

## Status: ✅ COMPLETE — the eval `pick` is proved, sorry-free, axiom-clean

`LeanEval.Geometry.PicksTheorem.pick` (the exact eval statement) is fully proved.
`#print axioms LeanEval.Geometry.PicksTheorem.pick` =
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. There is **no `sorry`**
anywhere in the engine or the bridge.

* **Pick's theorem in our engine**: `Pick.pick` (simple, positively-oriented
  `LatticePolygon` has `area = I + B/2 − 1`), sorry-free, axiom-clean.
* **The bridge to the eval statement is fully discharged** — every obligation
  below is proved:

| obligation (file)                       | content | status |
|-----------------------------------------|---------|--------|
| `boundary_bridge` (`EvalBridgeBoundary`) | Mathlib `Polygon.boundary` = our `LatticePolygon.boundary` under `Fin n ↔ ZMod n` | ✅ |
| `inside_eq` (`EvalBridgeInside`)         | topological interior `inside` = `{x ∉ ∂ ∧ winding ≠ 0}` (the polygonal Jordan identification) | ✅ |
| `ourPoly_isSimple` (`EvalBridgeSimple`)  | eval `IsSimple` ⇒ our `IsSimple` | ✅ |
| `reverseP_*` (`EvalBridgeReverse`)       | reversal preserves boundary/simplicity, negates winding (orientation WLOG) | ✅ |
| `eval_bridge` + `pick` (`EvalBridgeMain`)| packaging + `Nat.card = ncard` counts ⇒ the eval theorem | ✅ |

`inside_eq` (the genuinely new content) turned out tractable: it follows from
`exterior_reaches_far_beyond` (far-field reachability), local-constancy of
`winding` on `∂ᶜ`, and boundedness of the winding support — it did **not** need
the full ≤2-component theorem.

---

## Repo / submission structure

```
Submission/Engine/                 -- self-contained proof engine + bridge (bundled)
  Defs Winding Area Weight PerEdge Jordan Pick            -- core engine (namespace Pick)
  Pick/ Reductions Alternation Corners BoundaryArcs Slab Routing EarClip
  EvalBridge           -- base: eval helpers (verbatim) + `ourPoly`
  EvalBridgeBoundary   -- boundary_bridge
  EvalBridgeInside     -- inside_eq  (Jordan identification)
  EvalBridgeSimple     -- ourPoly_isSimple
  EvalBridgeReverse    -- reverseP_boundary / _winding / _isSimple
  EvalBridgeMain       -- eval_bridge + the eval `pick`   ← the proved theorem
```

The engine is ~28k lines across 15 modules (namespace `Pick`); the bridge adds
6 small modules (namespace `LeanEval.Geometry.PicksTheorem`, plus a few
`Pick.reverseP_*` lemmas). Everything is self-contained against Mathlib.

## Assembling the submission

1. **Bundle** (rewrites `JordanPick.PicksTheorem` → `Submission.Engine`):
   ```
   ./bundle-engine.sh /path/to/jordan_pick
   ```
   Populates `Submission/Engine/` with the 14 engine modules + 6 bridge modules
   (all proved, sorry-free).

2. **Wire the trusted helpers.** `EvalBridge.lean` *defines* the eval helpers
   (`toPlane`, `latPoly`, `inside`, `area`, `Adjacent`, `IsSimple`,
   `boundaryPts`, `interiorPts`) so the tree compiles standalone. In the real
   submission these are **trusted** — they live in the eval's `Challenge.lean`,
   same namespace `LeanEval.Geometry.PicksTheorem`. To avoid duplicate
   definitions, delete that `def` block from `EvalBridge.lean` and `import` the
   challenge file instead (leaving only `ourPoly` + lemmas). Then place the
   proof of `pick` where the eval harness expects it — either keep
   `EvalBridgeMain`'s `pick` and point `Solution.lean` at it, or move the
   one-line proof body into the harness's `Submission.lean`.

3. **Build** with `lake build` and confirm
   `#print axioms LeanEval.Geometry.PicksTheorem.pick` shows no `sorryAx`
   (verified locally: `[propext, Classical.choice, Quot.sound]`).

## ⚠️ Toolchain risk — check this first

Our engine + bridge are verified against **Lean `v4.31.0`** + **Mathlib
`v4.31.0`** (`lean-toolchain` is copied here). The proof is complete *at this
pin*. The lean-eval harness pins its *own* Mathlib version, and the bundled
~28k-line engine must compile there. **If lean-eval's pin differs from
`v4.31.0`, expect Mathlib API-drift breakage** in the engine. Confirm the
eval's `lean-toolchain` / `lake-manifest` Mathlib revision; if it differs,
either pin the submission workspace to `v4.31.0` (if the harness allows) or
budget for an engine port to the harness's Mathlib.
