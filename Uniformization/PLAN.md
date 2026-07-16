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
