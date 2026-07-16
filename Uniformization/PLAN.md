# Uniformization — formalization plan

**Status (2026-07-16): STATEMENTS COMPILE (`sorry`), plan re-scoped around
lean-eval PR #473 and mathlib4 PR #33505.** Nothing proved yet. Both problems
**UNSOLVED on the leaderboard by anyone** (incl. Aristotle, Seed Prover).

## Two targets (lean-eval, submitter Junyan Xu)

[lean-eval PR #473](https://github.com/leanprover/lean-eval/pull/473) (open, by
the problem submitter) added a second, "possibly easier" problem
`uniformization_key` next to the original `uniformization`. Both are mirrored
exactly in `Uniformization/Main.lean` (typechecked against the pin: Lean
`v4.32.0-rc1`, Mathlib `360da6f`); the PR's diff is vendored at
`reference/uniformization/lean-eval-pr473.diff`.

**Primary target — `uniformization_key`** (Anghel–Stan arXiv:2008.12189,
text in `reference/rado/anghel-stan.txt`):

```lean
theorem uniformization_key (hX : ¬ CompactSpace X) [SimplyConnectedSpace X] :
    ∃ D : TopologicalSpace.Opens ℂ, Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ D)
```

A connected, noncompact, second countable, **simply connected** Riemann surface
is biholomorphic to **some open subset of ℂ** — no ℂ-vs-disk dichotomy, no
`H¹(X,ℝ)=0` decoding, and the target is any planar domain. Manifest note: "a
key step … which just needs to be combined with the Riemann mapping theorem and
Radó's theorem to yield a full proof."

**Secondary — `uniformization`** (Hubbard Thm 1.1.2, unchanged semantically):

```lean
theorem uniformization (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane)
```

Deriving `uniformization` from `uniformization_key` needs: planar RMT applied
to the resulting domain `D` (simply connected as a biholomorph of `X`; `D ≠ ℂ`
case → disk → upper half plane), plus the glue `H¹(X,ℝ)=0 ⇒ SimplyConnectedSpace`
for noncompact surfaces (π₁ of an open surface is free; a free group with no
nontrivial homs to ℝ is trivial) — this glue is itself nontrivial, so treat the
two problems independently and go after `uniformization_key` first.

## The game changer: RMT is no longer a from-scratch build

[mathlib4 PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505)
(urkud, draft, +974 lines, **sorry-free**) proves the planar Riemann mapping
theorem: `exists_bijOn_unitBall_map_eq_zero` — for `U ⊆ ℂ` open, simply
connected, `≠ univ`: a holomorphic bijection `U → ball 0 1`. En route it builds
exactly what our old gap analysis flagged as missing:

- **Montel-style compactness**: `equicontinuousAt_of_forall_norm_le`,
  `uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le` + Ascoli
  (`Topology/UniformSpace/Ascoli` is already in the pin).
- **Hurwitz theorems**: `eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn`,
  `eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn` (injectivity of locally
  uniform limits — needed for our limit assembly, not just for RMT).
- **Branch of log / n-th root** on simply connected sets (`exists_branch_log`,
  `exists_branch_nthRoot`).
- Möbius shifts of the unit disc (new file `UnitDisc/Shift.lean`).

Full sources vendored in `reference/uniformization/` with porting notes. All its
imports **exist at our pin** except its own new file; porting = strip the new
`module`/`public` keywords + routine API drift. Backup source:
[vbeffara/RMT4](https://github.com/vbeffara/RMT4) (complete standalone RMT,
older pin).

**First concrete milestone: port PR #33505 to the pin as `Uniformization/RMT/`**
(audit `#print axioms` after port; PR is a draft with possible dependencies on
unmerged PRs — resolve drift against the pin as it surfaces).

## Proof route for `uniformization_key` (A–S §4–7)

Per PR #473's docstring, A–S prove exactly this statement, using Sard + planar
RMT to bypass Hubbard's heavier prerequisites. Sources: `anghel-stan.txt`,
`hubbard-ch1.txt` in `reference/rado/`.

1. **Green's function** (A–S Prop 9). On compact simply-connected `K ⊂ X` with
   smooth boundary and `x₀ ∈ K°`: Perron family with `−log|ξ|` barrier gives
   `G : K∖{x₀} → [0,∞)`, harmonic on `K°∖{x₀}`, `0` on `∂K`, log pole at `x₀`.
   *Reuses:* Perron + Dirichlet + barriers from `Rado/`.
2. **Removable singularity** (A–S Lemma 8). Bounded harmonic on `D∗` extends.
   Via conjugate + `exp` + Mathlib's holomorphic removable singularity.
3. **Biholomorphism onto a subdomain of D** (A–S Thm 10). `ϕ = e^{−G−iF}`,
   `F` integrating the conjugate 1-form; period `−2π` (Stokes + log-pole
   residue) makes `ϕ` single-valued into `D`; injective via argument principle.
   Gives `K° ≃ ϕ(K°) ⊆ D`. *Uses:* `Rado/Surface/Germs`, argument principle.
4. **Planar RMT** (A–S Thm 11). Upgrade to `K° ≃ D`. ← **from ported PR #33505**
   (note: its `BijOn` form needs packaging as a biholomorphism; inverse is
   holomorphic by open mapping / inverse function theorem).
5. **Compact exhaustion** (A–S Thm 12). Noncompact + s.c. + simply connected ⇒
   exhaustion `K₀ ⊂ K₁ ⊂ …` by compact simply-connected sets with smooth
   boundary. Proper smooth function + **Sard** regular values + hole-filling.
   ⚠ Sard on manifolds: check pin; likely the main remaining infrastructure gap.
6. **Limit assembly** (A–S Lemma 13 + Thm 1). Normalized `φₙ : Kₙ° ≃ rₙD`
   (Green's-function monotonicity + Harnack control the normalization);
   Montel + diagonal extraction → loc. uniform limit `φ`; Hurwitz ⇒ injective;
   `φ : X ≃ φ(X)` open ⊆ ℂ. Package as `X ≃ₘ⟮mℂ, mℂ⟯ D` with
   `D := ⟨φ '' univ, …⟩ : Opens ℂ` (holomorphic + injective ⇒ `ContMDiff` equiv
   both ways). *Montel/Hurwitz from step-4 port.* No Carathéodory kernel
   machinery needed for the key statement (no canonical target to hit).

## Design decisions v2 (2026-07-16) — no Sard, no Stokes, no van Kampen

A–S use Sard twice (Thm 10 period quantization; Thm 12 smooth exhaustion).
Both are engineered away:

1. **φ-existence via a covering over the UNPUNCTURED piece (replaces the
   period argument entirely).** For `G` a Green's function of a piece `V` with
   pole `x₀`, build the étale space `E → V` of local holomorphic `ψ` with
   `‖ψ‖ = exp (−G)` — with domains allowed to CONTAIN `x₀` (where `ψ` has a
   simple zero, locally `ψ = ξ·e^{−H−iH̃}`). Key miracle: over the punctured
   chart disk EVERY branch extends across `x₀`, because the ratio of two
   branches is a holomorphic `S¹`-valued function, hence locally constant —
   the integer residue of the log pole in multiplicative disguise. So the
   fibers are discrete `S¹`-torsors everywhere and `E → V` is an honest
   covering map of ALL of `V`. `V` simply connected ⇒ global section (path
   lifting + monodromy; pin has `Topology/Homotopy/Lifting` + `IsCoveringMap`)
   ⇒ global holomorphic `φ` with `‖φ‖ = e^{−G}`, `φ(x₀) = 0`. No periods, no
   winding numbers, no grid. Machinery mirrors `Rado/Surface/Germs.lean`
   (étale space of conjugate germs) in multiplicative form.
2. **Exhaustion pieces = finite unions of closed chart disks with generic
   radii** (no smooth boundary, no Morse, no Sard). Tangency radii between a
   circle and an analytic curve are critical values of an analytic function ⇒
   countable ⇒ avoidable. Transversal corners ⇒ every frontier point has an
   **exterior disk** (`ExteriorDiskAt`, `Uniformization/Surface/Regularity.lean`)
   ⇒ log-barrier ⇒ Dirichlet-regular, which is all Perron/Green needs.
3. **The topological heart (W7), isolated:** in a simply connected `X`, a
   generic-disk-union piece hole-fills/enlarges to a **simply connected**
   piece (Kerékjártó-style). Plan: the boundary of a complement component is a
   finite union of circular arcs meeting at generic corners ⇒ decompose into
   explicit **arc-cycles** (combinatorial tracing, no Jordan curve theorem);
   connectivity of each component's boundary via a **crossing-parity**
   argument: an explicit collar of an arc-cycle (built by hand from disk
   geometry) gives a map `τ : X → S¹` with `τ = 1` off the collar; a loop
   crossing the arc-cycle once has winding `±1`, contradicting
   `SimplyConnectedSpace X` (winding is homotopy-invariant via circle-covering
   lifting — pin machinery). Then the A–S Tietze retraction (`X → K̂` collapsing
   each complement end onto its boundary arc-cycle) gives `π₁(K̂°) = 1`.
4. **Assembly without RMT-normalization risk:** with simply connected pieces,
   `φₙ : Vₙ ≃ D` via ported RMT; hyperbolic case (radii bounded) needs only
   Schwarz + Montel + Hurwitz; parabolic case (radii → ∞) needs **Koebe
   quarter + distortion (W6)** — A–S's Lemma 13 as printed has a glossed step
   ("easy to see" uniform disk at `−i`) that is a hidden Koebe-type input, so
   we build Koebe honestly: area theorem → Bieberbach `|a₂| ≤ 2` → quarter +
   distortion (planar power-series/Parseval work, independently valuable).

### Reuse from `reference/jacobian-fable` (surveyed 2026-07-16, sorry-free)
- `Jacobian/Path/*`: integration-free `pathIntegral` (primitive-difference),
  homotopy invariance, `Periods.lean`, `Perturb.lean` loop-avoidance —
  compactness-free, portable; useful for W7/W2 alternatives and M5.
- `Jacobian/AbelWeak/PlanarLogBranch.lean`: `exists_logBranch_disk`,
  `exists_exteriorLogBranch` — pure ℂ, portable.
- `Jacobian/PlanarStokes/*`: compact-support ∂̄ = 0, annulus residue atoms.
- `Jacobian/SphereTopology/SimplyConnectedP1.lean`: two-cap simple-connectivity
  pattern (template for `OnePoint`-style arguments in M5's dichotomy).
- NO surface topology (no homology/classification/retraction) — W7 must be built.

### Reuse from `reference/classification-of-surfaces` (surveyed 2026-07-16)
The lean-eval classification project (Lean v4.31.0; 2 sorries total, planar
Moise stack clean). NOT a drop-in for W7 — it has zero π₁/simple-connectivity
machinery and is straight-line-polygonal in `EuclideanSpace ℝ (Fin 2)`. Worth
taking:
- `Moise/PolygonalJordan.lean` (sorry-free): full **crossing-parity Jordan
  proof** (`index` = ray-crossing parity, `index_locallyConstant`,
  `exists_index_eq_one`) incl. frontier connectivity of complement components —
  the template for our arc-cycle sub-lemmas in W7 (b).
- `Moise/FrontierGlue.lean` (sorry-free, polymorphic over `X Y`): vanishing-
  error frontier collapse with continuity/injectivity/embedding — the exact
  shape of the A–S Tietze retraction step (W7 (c)); portable.
- `Moise/NoRetraction.lean`: `exists_radial_retraction_to_frontier` (Minkowski
  gauge retraction of punctured plane onto frontier of a convex body).
- `polygonal_schoenflies_rel`: identity-off-`U` straightening — architectural
  model for hole-filling normalizations.
Also a design option W7 could adopt: build pieces from chart **polygons**
instead of disks where that lets the polygonal templates apply verbatim
inside a single chart.

## What `Rado/` already gives us (reuse targets)

- `Rado/Complex/Poisson.lean`, `Dirichlet.lean` — Schwarz integral, Poisson
  extension, Dirichlet existence, MVP ⟺ harmonic, comparison.
- `Rado/Complex/SubMean.lean`, `Rado/Surface/Harmonic.lean` — sub/harmonic on
  ℂ-opens and chartwise on `X`, maximum principles.
- `Rado/Surface/Perron.lean` — **Perron's principle**, harmonic replacement,
  Harnack.
- `Rado/Surface/Barriers.lean` — log-barrier technique on annuli.
- `Rado/Surface/Germs.lean` — harmonic conjugates, rigidity, étale space of
  germs (the "integrate the conjugate differential" machinery for step 3).
- `Rado/Surface/Charts.lean` — holomorphic transitions, identity theorem,
  `HolomorphicOn`, local structure.

## Revised gap analysis

| Item | Old status | Now |
|---|---|---|
| Riemann Mapping Theorem | build from scratch | **port PR #33505** (sorry-free) |
| Montel / normal families | build from scratch | **in PR #33505** (Ascoli route) |
| Hurwitz / injective limits | check pin | **in PR #33505** |
| Carathéodory kernel convergence | build | **not needed** for `uniformization_key` |
| ℂ-vs-disk dichotomy | build | **not needed** for `uniformization_key` |
| Green's function on surfaces | build on `Rado/` Perron | unchanged (main original work) |
| Compact exhaustion + Sard | build | unchanged; Sard-on-manifolds = biggest pin gap |
| `H¹=0 ⇒ simply connected` glue | (implicit) | only for secondary target |

Estimated size drops from 15–30k to roughly **8–15k LOC** on top of `Rado/`'s
~5k, of which ~1k is the RMT port.

## Milestones (each independently valuable)

- **M0 RMT port**: PR #33505 → `Uniformization/RMT/` on the pin, axiom-audited.
  Mechanical; do first, unblocks 4 and 6.
- **M1 Green's functions** (Prop 9 + Lemma 8) on `Rado/` Perron.
- **M2 Biholomorphism `K° ≃ D`** (Thm 10 + ported RMT).
- **M3 Exhaustion** (Thm 12) — mostly independent; needs Sard.
- **M4 Limit assembly** (step 6) + `Diffeomorph`/`Opens` packaging ⇒
  **`uniformization_key` done**.
- **M5 (stretch) full `uniformization`**: key + RMT dichotomy + `H¹=0 ⇒
  SimplyConnectedSpace` glue.

## Potential source repos for the missing analytic pieces

Two prior AI-generated formalizations targeting **Abel's theorem / the Jacobian
of a compact Riemann surface** carry much of the complex-analytic machinery
(∂̄, Cauchy kernels, removable singularities, log branches, Stokes pairings):

- **https://github.com/rkirov/jacobian-claude** (Claude) and
  **https://github.com/rkirov/jacobian-fable** (Fable 5 rerun, with a minimal
  blueprint summary).

Likely-reusable modules: `Dbar/` (∂̄ operator, `CauchyKernel`, `SolveDisk`,
`DiskAcyclic`, Wirtinger, planar Cousin), `CanonicalForms/FormRemovableSingularity.lean`
(A–S Lemma 8), `Abel/LogPiece.lean` + `AbelWeak/PlanarLogBranch.lean` (log
pole/period, step 1 & 3), `Abel/AreaPairing.lean` + `AbelPairingStokes.lean` +
`SerreFunctional.lean` (Stokes/periods, step 3), `Cech/` + `DolbeaultComparison/`
(cohomology vanishing).

⚠ **Caveats:** AI-generated, unreviewed — audit `#print axioms` + `sorry` sweep
before trusting anything. Older pins (`v4.30.0` / `v4.30.0-rc2`), need porting.
Compact-surface statements need adapting.

## Submission mechanics

Same as Radó: bundle a workspace with `Submission.lean` declaring the theorem;
comparator restricts to `propext, Quot.sound, Classical.choice`. See
`generated/uniformization/` in `leanprover/lean-eval` and
`scripts/make_rado_submission.sh`. Note `uniformization_key`'s manifest
(`manifests/problems/uniformization_key.toml`, in the vendored diff) — once PR
#473 lands, the problem id is `uniformization_key`, module
`LeanEval.Geometry.Uniformization`, hole `uniformization_key`.
