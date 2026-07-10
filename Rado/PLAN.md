# Radó's theorem — formalization plan

**Target** (lean-eval [`rado_riemannSurface`](https://lean-lang.org/eval/problems/rado_riemannSurface/),
submitter Junyan Xu, source Hubbard *Teichmüller theory* Vol. 1 §1.3):

```lean
theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X
```

Every connected Hausdorff Riemann surface is second countable. The real
analogue is **false** (Prüfer surface, long line), so the complex structure
must be used essentially. Harness pins match this repo exactly
(Lean `v4.32.0-rc1`, Mathlib `360da6f`); submissions must use only the three
standard axioms. The two recorded eval solutions (Aristotle/Harmonic 2026-06-22,
Seed Prover/ByteDance 2026-06-28) are **private**; the only public attempt
(Vilin97/aleph, `reference/rado/aleph_rado.lean`) proved the easy reductions
and left the core as `sorry`. Junyan Xu (Zulip, 2026-07-09): the reference
proof needs "a nontrivial amount of materials about Riemann surfaces, Perron
method, and universal cover" — and he'd like the theorem in Mathlib.

## Proof route ("A′": Hubbard/Forster, trimmed)

Sources: Anghel–Stan arXiv:2008.12189 (most self-contained; follows Hubbard),
Rainer's Vienna notes §22–23 (= Forster §22–23, complete proofs),
Hubbard Ch. 1 free excerpt. All in `reference/rado/`.

Setup: pick a chart `φ : U₀ ≅ open ⊆ ℂ` whose image contains a large ball;
inside it two disjoint closed coordinate disks `K₀, K₁` with surrounding
closed annuli. Let `Y := X ∖ (K₀ ∪ K₁)`, open, connected, nonempty.

1. **Dirichlet on a disk** (deepest ℂ-level analytic input). The Schwarz
   integral `S[f](z) = ⨍ herglotzRieszKernel · f` of continuous boundary data
   `f : sphere c R → ℝ` is holomorphic on the ball with `Re S[f] = P[f]` the
   Poisson integral; `P[f] → f` at the boundary (positive kernel, unit mass,
   approximate identity). Corollaries: harmonic ⟺ continuous + circle-MVP;
   harmonic conjugates exist on disks. Mathlib pin already has
   `herglotzRieszKernel`/`poissonKernel` + two-sided kernel bounds +
   representation of harmonic functions (`Mathlib/Analysis/Complex/Poisson.lean`,
   `.../Harmonic/{MeanValue,Analytic,Poisson}.lean`) — missing is exactly
   "Poisson integral of *given* boundary data is harmonic + attains the data".
2. **Subharmonic on ℂ-opens** (comparison definition: `g ≤ h` on `∂D` ⇒ on `D`,
   for harmonic `h`, over compact subdisks; equivalent to sub-MVP —
   Anghel–Stan Prop. 3). Maximum principle (clopen argument), closure under
   `max`, harmonic replacement on subdisks, invariance under holomorphic maps.
3. **Surface layer**: chartwise harmonic/subharmonic on `X`-opens; invariance
   under chart transitions (holomorphic by C¹-over-ℂ + `DifferentiableOn.analyticOnNhd`).
4. **Perron**: `F := {g : subharmonic on Y, values in [0,1], ≤ 0 near ∂K₀, ≤ 1}`;
   `u := sup F` is harmonic on `Y` (Anghel–Stan App. A proof is Harnack-free:
   monotone limits + area-MVP + DCT; alternatively Harnack from the pinned
   Poisson-kernel bounds).
5. **Nonconstancy via explicit log-barriers** (trims Hubbard 1.2.4 / Forster
   22.7–22.8 boundary regularity): on the annulus around `K₁` the function
   `max(0, log(R₁/|ζ−c₁|)/log(R₁/r₁))` is a Perron-family member forcing
   `u > 3/4` near `∂K₁`; the harmonic `1 − log(R₀/|ζ−c₀|)/log(R₀/r₀)` dominates
   every member on the annulus around `K₀`, forcing `u < 1/4` near `∂K₀`.
6. **Étale space of conjugate germs** (replaces the universal cover; cf.
   Forster Thm 8.5): for open `V ⊆ Y` let `C(V) := {F : V → ℂ holomorphic with
   Re F − u locally constant}`. Existence on coordinate disks (Schwarz integral
   in the chart), rigidity on connected `V` (two members differ by a constant).
   `X̂ := {(y, germ_y F)}` with basic opens `⟨V,F⟩`; projection `p` is a local
   homeo, trivialized over coordinate disks; `X̂` Hausdorff (identity theorem).
   Evaluation `E(y, germ F) = F y` is continuous with **discrete fibers**
   (else `u` is locally constant somewhere, hence — clopen argument + identity
   theorem — constant on `Y`, contradicting 5).
7. **Poincaré–Volterra lemma** (pure topology; Forster/Rainer 23.2): a
   connected Hausdorff, locally compact, locally connected, locally
   second-countable space with a continuous discrete-fiber map to a
   second-countable Hausdorff space is second countable. Proof: basis =
   second-countable components of preimages of basic sets; ccc bounds
   neighbours; chain-reachability + clopen argument.
8. **Assembly**: `X̂₀` (a component) is second countable by 7; `p|X̂₀` is an
   open continuous surjection onto `Y` (component-of-covering + `Y` connected),
   so `Y` is second countable (`Topology.IsQuotientMap.secondCountableTopology`);
   `X = Y ∪ U₀`, both second countable ⇒ done
   (`secondCountableTopology_of_countable_cover`).

## Modules (import DAG, roughly bottom-up)

**STATUS (2026-07-10): COMPLETE.** All modules sorry-free;
`#print axioms rado_riemannSurface = [propext, Classical.choice, Quot.sound]`.
Submission workspace: `submission/rado_riemannSurface/`
(regenerate with `scripts/make_rado_submission.sh`).

| file | content | status |
|---|---|---|
| `Rado/Topology/SecondCountable.lean` | compact ⇒ s.c. in locally-s.c. spaces; countable unions; ccc; reachability | ✅ |
| `Rado/Topology/PoincareVolterra.lean` | step 7 | ✅ |
| `Rado/Complex/SubMean.lean` | sub-mean-value functions, maximum principles | ✅ |
| `Rado/Complex/Poisson.lean` | step 1: Schwarz integral, Dirichlet existence | ✅ |
| `Rado/Complex/Dirichlet.lean` | step 1 packaging: `poissonExtension`, MVP ⟺ harmonic, comparison | ✅ |
| `Rado/Complex/PlanarConnected.lean` | ball minus two closed disks is connected (config: unit disks at `±4` in `B(0,8)`) | ✅ |
| `Rado/Surface/Charts.lean` | holomorphic transitions from C¹; identity theorem; instances | ✅ |
| `Rado/Surface/Harmonic.lean` | step 3: chartwise sub/harmonic functions; `SubMeanLocalOn` local-to-global bridge | ✅ |
| `Rado/Surface/Perron.lean` | step 4: harmonic replacement (T2 counterexample recorded), Harnack, Perron's principle | ✅ |
| `Rado/Surface/Barriers.lean` | step 5: two-disk configuration, log-barriers, witness values | ✅ |
| `Rado/Surface/Germs.lean` | step 6: conjugates (`Re F = u`), rigidity, étale space, discrete-fiber evaluation | ✅ |
| `Rado/Surface/Assembly.lean` | step 8: Poincaré–Volterra application, descent, final cover | ✅ |
| `Rado/Main.lean` | the exact eval statement | ✅ |

Noteworthy proof facts discovered during formalization:
* holomorphy of the Schwarz integral needs no differentiation under the
  integral: on the sphere the Herglotz kernel is `2(z-c)/(z-w) − 1`, so the
  Schwarz integral is an affine function of a Cauchy integral, and Mathlib's
  `hasFPowerSeriesOn_cauchy_integral` applies directly;
* the replacement-subharmonicity lemma (A–S Remark 4) genuinely needs
  Hausdorffness: on the line-with-doubled-origin surface the replacement disk
  is not closed and the glued function is discontinuous at the doubled origin
  (counterexample recorded at `surfaceReplace_surfaceSubharmonicOn`).

Design choices that trim the classical proof (record for the blueprint):
subharmonicity is *defined* chartwise over the maximal atlas (all charts, all
circles), so no `subharmonic ∘ holomorphic` invariance is ever needed — only
`HarmonicOnNhd.comp_analytic`; conjugates are normalized `Re F = u` exactly, so
sheets differ by *imaginary* constants and local triviality of the étale
projection is CR-elementary (no identity theorem needed for triviality, only
for Hausdorffness and fiber discreteness); the Perron family is `[0,1]`-valued
(sSup stays finite trivially); nonconstancy comes from the two explicit
log-barriers on the annuli `1 ≤ |ζ ∓ 4| ≤ 2` with witness points at
`±4 + 2^(1/4)` (values `≥ 3/4` resp. `≤ 1/4`).

Estimated total ≈ 3–5k LOC. Highest-risk items: Poisson boundary continuity
(1), subharmonic gluing bookkeeping (2), étale-space topology (6). Pure
topology (7, 8) is low-risk and independent — good parallel work.

## Submission mechanics (when sorry-free)

Bundle into a workspace `rado_riemannSurface/` with `lakefile.toml`
(`name = "rado_riemannSurface"`), `Submission.lean` declaring
`Submission.rado_riemannSurface`, helpers under `Submission/`; submit via
issue at `leanprover/lean-eval` (template `submit.yml`). Comparator rejects
any axiom beyond `propext, Quot.sound, Classical.choice`. See
`reference/rado/harness/` and `scripts/make_jordan_submission.sh` for the
prior bundling pattern.
