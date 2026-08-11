# jordan_pick

A clean-room Lean 4 / Mathlib formalization of **Pick's theorem** (Freek's
*Formalizing 100 Theorems* #92), the **polygonal Jordan curve theorem**, the
full **(continuous) Jordan curve theorem**, and **Radó's theorem** (every
connected Hausdorff Riemann surface is second countable) — all genuinely
missing from Mathlib.
Three lean-eval problems are solved: [`pick`](https://lean-lang.org/eval/problems/pick/),
[`jordan_curve`](https://lean-lang.org/eval/problems/jordan_curve/), and
[`rado_riemannSurface`](https://lean-lang.org/eval/problems/rado_riemannSurface/).

## Main results

All proved **sorry-free**; `#print axioms` shows only the three standard axioms
`[propext, Classical.choice, Quot.sound]`.

| theorem | location | statement |
|---|---|---|
| **Pick's theorem** | `Pick.pick` (`JordanPick/PicksTheorem/Pick.lean`) | a simple, positively-oriented lattice polygon has `area = I + B/2 − 1` (area = Lebesgue measure of the winding interior; `I`/`B` interior/boundary lattice-point counts) |
| **Polygonal Jordan curve theorem** | `Pick.compl_boundary_atMost_two` (`JordanPick/PicksTheorem/Pick.lean`) | the complement of a simple polygon's boundary has at most two connected components, with the winding number locally constant `∈ {0, 1}` |
| **lean-eval Pick** | `LeanEval.Geometry.PicksTheorem.pick` (`JordanPick/PicksTheorem/EvalBridgeMain.lean`) | the exact statement of <https://lean-lang.org/eval/problems/pick/> (Mathlib `Polygon`, *topological* interior, no orientation hypothesis), bridged to `Pick.pick` |
| **Jordan curve theorem (continuous)** | `JordanCurve.jordan_curve` (`JordanPick/JordanCurve.lean`) | the exact statement of <https://lean-lang.org/eval/problems/jordan_curve/>: a continuous injection `S¹ → ℝ²` has a complement with exactly two connected components (`Nat.card (ConnectedComponents (range r)ᶜ) = 2`) |
| **Brouwer fixed point theorem (2D)** | `JordanCurve.Brouwer.brouwerFPT` (`JordanPick/JordanCurve/Brouwer.lean`) | every continuous self-map of a nonempty compact convex subset of `ℝ²` has a fixed point |
| **Radó's theorem** | `rado_riemannSurface` (`Rado/Main.lean`) | the exact statement of <https://lean-lang.org/eval/problems/rado_riemannSurface/>: a connected Hausdorff `ChartedSpace ℂ` with `IsManifold 𝓘(ℂ) 1` is `SecondCountableTopology` |
| **Poincaré–Volterra lemma** | `Rado.poincare_volterra` (`Rado/Topology/PoincareVolterra.lean`) | a connected Hausdorff, locally compact, locally connected, locally second-countable space with a continuous discrete-fiber map to a second-countable Hausdorff space is second countable |
| **Dirichlet problem on a disk** | `Rado.exists_harmonic_extension` (`Rado/Complex/Poisson.lean`) | continuous boundary data on a circle extends continuously to the closed disk, harmonically inside |
| **Perron's principle** | `Rado.IsPerronFamily.surfaceHarmonicOn_perronSup` (`Rado/Surface/Perron.lean`) | the upper envelope of a Perron family on a Riemann surface is harmonic |

The **Radó development** (`Rado/`, separate `lean_lib`) is a distinct project
from Pick/Jordan: Perron's method on an explicit two-disk configuration
produces a nonconstant harmonic function; the étale space of its
harmonic-conjugate germs has an evaluation map with discrete fibers; the
Poincaré–Volterra lemma plus descent give second countability. Plan and
module map: `Rado/PLAN.md`; submission workspace:
`submission/rado_riemannSurface/` (`scripts/make_rado_submission.sh`).

## Approach

The spine is the **winding number** as a per-edge signed ray-crossing sum (pure
integer arithmetic — no transcendental angles, no general topology). From it:
`area = ∫∫ winding` (Green) `= shoelace`; the polygonal Jordan curve theorem
gives `winding ∈ {0,1}`; and **ear-clipping induction** (the Meisters two-ears
theorem, via a deepest-contained-vertex diagonal split with a non-circular
winding-jump separation argument) reduces the area identity to the triangle
case.

The lean-eval Pick target adds a bridge: Mathlib `Polygon` ↔ our `LatticePolygon`,
the topological interior ↔ the winding interior, an orientation WLOG (vertex
reversal), and lattice-count matching.

The **continuous Jordan curve theorem** is a separate development (it does *not*
use the polygonal one): **Maehara's proof** — reduce the separation statement to
the **Brouwer fixed point theorem** via two lemmas (a crossing lemma for
transversal paths in a rectangle, and "each component has the curve as its
boundary"), plus the farthest-pair normalization and the `l,m,p,q,z₀`
construction that pins down exactly one bounded component. Brouwer FPT for `ℝ²`
is then built from the ground up: `π₁(S¹) ≅ ℤ` → no retraction of the disk onto
its boundary → Brouwer on the disk (ray-retraction) → the general convex-compact
case (nearest-point projection).

## Building

```
lake build
```

Pinned to **Lean `v4.33.0`** + **Mathlib `db584cd6`** (the `v4.33.0` release tag)
via `lean-toolchain` / `lakefile.toml`. Mathlib is fetched as a dependency.

`v4.33.0` carries both of the mid-2026 kernel soundness fixes —
[#14484](https://github.com/leanprover/lean4/issues/14484) (missing closure check
on `opaque` declarations), first released in `v4.32.1`, and
[#14576](https://github.com/leanprover/lean4/issues/14576) (nested inductives with
phantom parameters escaping the type checker), first released in `v4.32.2`. Both
were reachable only by an adversarial metaprogram calling `addDecl` directly,
never from ordinary tactics, but the axiom audits below are worth more on a kernel
that has them.

The development has been ported forward repeatedly and is fairly version-robust,
though not free: `v4.31.0` → `v4.32.0-rc1` needed no changes at all;
`v4.32.0-rc1` → `v4.32.2` needed one mechanical rename (`LocPathConnectedSpace` →
`LocallyPathConnectedSpace`); `v4.32.2` → `v4.33.0` cost rather more. Lean 4.33
matches `rw`/`simp` patterns at *reducible* transparency, and this development
builds several `LatticePolygon`s whose `n` field is defined from another
polygon's (`shearP`, `linP`, `deleteLast`, `rotateP`). `ZMod (shearP P k).n` and
`ZMod P.n` are definitionally equal but not reducibly so, and rewrites that used
to fire silently across that gap stopped firing. The repairs are marked in place;
alongside them, Mathlib's `Set.setOf` → `Set.ofPred` and `Set.restrict` →
`Set.domRestrict` renames account for the rest of the diff.

## Layout

```
JordanPick/PicksTheorem/
  Defs Winding Area Weight PerEdge Jordan      -- winding/area/count primitives
  Pick/ Reductions Alternation Corners BoundaryArcs Slab Routing EarClip
  Pick.lean                                    -- the JCT + ear-clipping + Pick.pick
  EvalBridge*                                  -- the bridge to the lean-eval statement
submission/                                    -- self-contained lean-eval submission scaffold
```

## lean-eval submission

`submission/` holds a turnkey scaffold for the lean-eval Pick problem:
`bundle-engine.sh` bundles the engine + bridge into a self-contained
`Submission/Engine/` tree (no external project import), and `README.md` there
documents the assembly. See it for the (logistics-only) remaining steps.

## Notes

* **Clean-room.** Developed independently of the existing unlicensed Lean Pick
  repository.
* Area is the rigorous Lebesgue measure of the enclosed region, not
  shoelace-as-definition.

## Relation to prior work

Clean-room with respect to proofs, with prior art credited explicitly:

* The **geometric core** — the polygonal Jordan curve theorem and the
  ear-clipping (Meisters two-ears) reduction that yield `Pick.pick` — is
  original. The closest prior Lean attempt (Eisermann, below) proves
  only the *algebraic* count identity and leaves the geometric half (a
  winding/Umlaufsatz argument) unproved (`sorry`).
* The **count side** (`latWeight` / `latWeightSum` in `Weight.lean`) follows the
  discrete-angle-weight device of Eisermann (`dang` / `Welp`); the
  per-edge identity is proved independently here (a column decomposition rather
  than their four-box partition + reflection involution). See the `Weight.lean`
  header for specifics.
* The continuous JCT's **Maehara reduction** and the entire **Brouwer** chain
  (circle non-nullhomotopy, no-retraction, disk Brouwer, convex-compact) are
  original to this repo and self-contained against Mathlib. The one non-trivial
  topological input — that a once-around loop of the circle is not
  null-homotopic — is proved directly from Mathlib's covering-space path lifting
  (`AddCircle.isCoveringMap_coe` + `liftPath_apply_one_eq_of_homotopicRel`), so
  no external `π₁(S¹) ≅ ℤ` development is needed.

## License

[Apache-2.0](LICENSE). Machine-readable project metadata (sources, status,
axiom surface, automation) lives in [`formalization.yaml`](formalization.yaml).

## References

**Targets and tooling**
- Pick's theorem — [Wikipedia](https://en.wikipedia.org/wiki/Pick%27s_theorem)
- F. Wiedijk, *Formalizing 100 Theorems* (#92 is Pick) — <https://www.cs.ru.nl/~freek/100/>
- lean-eval Pick problem — <https://lean-lang.org/eval/problems/pick/>;
  source repo [`leanprover/lean-eval`](https://github.com/leanprover/lean-eval)
- [Mathlib](https://github.com/leanprover-community/mathlib4)

**Jordan curve theorem (polygonal)**
- T. C. Hales, *The Jordan Curve Theorem, Formally and Informally* —
  [PDF](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/hales1.pdf)
- C. Thomassen, *The Jordan–Schönflies Theorem and the Classification of
  Surfaces*, Amer. Math. Monthly 99(2):116–130, 1992 —
  [doi:10.1080/00029890.1992.11995820](https://doi.org/10.1080/00029890.1992.11995820)
  ([JSTOR](https://www.jstor.org/stable/2324180))

**Ear-clipping / triangulation (the reduction)**
- G. H. Meisters, *Polygons Have Ears*, Amer. Math. Monthly 82(6):648–651, 1975 —
  [doi:10.2307/2319703](https://doi.org/10.2307/2319703)
  ([open copy](https://digitalcommons.unl.edu/mathfacpub/54/))
- J. O'Rourke, *Computational Geometry in C*, 2nd ed., Cambridge Univ. Press, 1998
  (Lemma 1.3 / two-ears, §1.2)
- M. de Berg, O. Cheong, M. van Kreveld, M. Overmars, *Computational Geometry:
  Algorithms and Applications*, 3rd ed., Springer, 2008 (polygon triangulation)

**Prior formalizations of Pick's theorem**
- J. Harrison (HOL Light), *A formal proof of Pick's theorem*, Math. Struct.
  Comput. Sci., 2011 —
  [Cambridge Core](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/formal-proof-of-picks-theorem/6C09292039220C2215755FEFDB78818C)
- S. Binder & K. Kosaian (Isabelle/HOL), *Formalizing Pick's Theorem in
  Isabelle/HOL*, CICM 2024 — [arXiv:2405.01793](https://arxiv.org/abs/2405.01793);
  AFP entry [`Picks_Theorem`](https://www.isa-afp.org/entries/Picks_Theorem.html)
- M. Eisermann et al. (Lean), *Formalizing Pick's Theorem, efficiently*, 2026 —
  [arXiv:2603.23095](https://arxiv.org/abs/2603.23095)

**Background**
- O. Knill, *Some Fundamental Theorems in Mathematics* (Pick is §154) —
  [arXiv:1807.08416](https://arxiv.org/abs/1807.08416)
