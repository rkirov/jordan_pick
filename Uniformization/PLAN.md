# Uniformization theorem — formalization plan

**Target** (lean-eval [`uniformization`](https://lean-lang.org/eval/problems/uniformization/),
submitter Junyan Xu, source Hubbard *Teichmüller theory* Vol. 1, Ch. 1 — **Theorem 1.1.2**):

```lean
theorem uniformization {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold mℂ 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane)
```

A connected, noncompact, **second countable** Riemann surface with `H¹(X,ℝ)=0`
(encoded as `Subsingleton (Hom(π₁ X, ℝ))`) is biholomorphic to `ℂ` or to the
open disk (`≃ UpperHalfPlane`, the disk's Mathlib stand-in). Toolchain pins
match this repo (Lean `v4.32.0-rc1`, Mathlib `360da6f`); standard 3 axioms only.

**Status (2026-07-10): STATEMENT COMPILES (`sorry`).** `Uniformization/Main.lean`
holds the exact eval statement, typechecked against the pin. Nothing proved yet.
**UNSOLVED on the leaderboard by anyone** (incl. Aristotle, Seed Prover).

## Why the harness hands us second countability

§1.3 of Hubbard = Radó's theorem, already a separate LeanEval problem we solved
(`Rado/`). The harness assumes `[SecondCountableTopology X]` to avoid the overlap.
So we import/reuse the Radó development freely and never re-derive s.c.

## What `Rado/` already gives us (reuse targets)

- `Rado/Complex/Poisson.lean`, `Dirichlet.lean` — Schwarz integral, Poisson
  extension, Dirichlet existence, MVP ⟺ harmonic, comparison.
- `Rado/Complex/SubMean.lean`, `Rado/Surface/Harmonic.lean` — sub/harmonic on
  ℂ-opens and chartwise on `X`, maximum principles.
- `Rado/Surface/Perron.lean` — **Perron's principle** (`IsPerronFamily`,
  `surfaceHarmonicOn_perronSup`), harmonic replacement, Harnack.
- `Rado/Surface/Barriers.lean` — log-barrier technique on annuli.
- `Rado/Surface/Germs.lean` — harmonic conjugates (`IsConjugate`, `Re F = u`
  exactly), rigidity, étale space of germs — the machinery behind "integrate
  the conjugate differential to a (locally) holomorphic function."
- `Rado/Surface/Charts.lean` — holomorphic transitions, identity theorem,
  `HolomorphicOn`, local structure.

## Proof route (Anghel–Stan arXiv:2008.12189 §4–7 = Hubbard §1.4–1.7)

Sources in `reference/rado/`: `anghel-stan.txt` (self-contained), `hubbard-ch1.txt`.

1. **Green's function** (A–S Prop 9). On a compact simply-connected `K ⊂ X` with
   one smooth boundary component and `x₀ ∈ K°`, a Perron family with a
   `−log|ξ|` barrier yields continuous `G : K∖{x₀} → [0,∞)`, harmonic on the
   interior, `0` on `∂K`, logarithmic pole at `x₀` (`G + log|ξ|` harmonic near
   `x₀`). *Reuses:* Perron + Dirichlet + barriers from `Rado/`.
2. **Removable singularity** (A–S Lemma 8). A harmonic function on `D∗` bounded
   near `0` extends harmonically across `0`. Via conjugate + `exp` + Mathlib
   holomorphic removable singularity. *Partly new.*
3. **Biholomorphism onto a subdomain of D** (A–S Thm 10). `ϕ = e^{−G−iF}` where
   `F` integrates the conjugate 1-form `JdG`; the period is `−2π` (Stokes +
   residue of the log pole), so `ϕ` is single-valued into `D`; injective by
   open-mapping + local `z ↦ cz^k` structure; `ϕ(x₀)=0`. Gives
   `K° ≃ ϕ(K°) ⊆ D`. *Uses:* `Rado/Surface/Germs`, argument principle, Sard.
4. **Riemann Mapping Theorem** (A–S Thm 11). Upgrade `ϕ(K°) ⊆ D` to `K° ≃ D`.
   ⚠ **NOT IN MATHLIB** (`Mathlib/Analysis/Complex/RiemannMapping.lean` has only
   steps 1–2). Must be built. Depends on Montel (§6).
5. **Compact exhaustion** (A–S Thm 12). `X` noncompact s.c. ⇒ exhaustion
   `K₀ ⊂ K₁ ⊂ …`, each compact simply-connected with connected smooth boundary.
   Via a proper Morse function (partition of unity from s.c.), Sard regular
   values, hole-filling, and a Tietze retraction to kill `π₁`. *Uses:* the given
   second countability. `H¹=0`/simply-connected enters here (kills periods).
6. **Montel / normal families.** ⚠ **NOT IN MATHLIB.** Locally bounded families
   of holomorphic functions are precompact in `O(D)` (loc. uniform topology).
   Needed for §4 and §7.
7. **Carathéodory kernel convergence + assembly** (A–S Lemma 13 + end of Thm 1).
   Normalize `φₙ : Kₙ° ≃ rₙD`; diagonal-extract a loc. uniform limit `φ : X → ℂ`;
   Hurwitz/argument-principle injectivity ⇒ `φ` biholomorphism onto its image.
8. **ℂ-vs-disk dichotomy + packaging.** Decide `image = ℂ` vs bounded, produce
   `Diffeomorph mℂ mℂ X ℂ ∞` or `… UpperHalfPlane`. Package holomorphic ⇒ `ContMDiff ∞`.

## Mathlib gap analysis (the hard truth)

Critical-path items **absent from the pin**, each a substantial project:
- **Riemann Mapping Theorem** (full) — only partial results present.
- **Montel's theorem / normal families / `O(D)` topology.**
- **Sard's lemma on manifolds** (needed §3, §5) — check pin; likely partial.
- **Green's functions on Riemann surfaces** — none; build on `Rado/` Perron.
- **Kernel/Carathéodory convergence, Hurwitz's theorem** — check pin.

Present and reusable: Poisson/Dirichlet (Mathlib + `Rado/`), argument principle
(`Mathlib/Analysis/Complex/…`), `UpperHalfPlane` manifold structure,
`FundamentalGroup`, `Diffeomorph`.

## Rough size / risk

Estimated **15–30k LOC** on top of `Rado/`'s ~5k. Highest-risk (research-grade)
milestones: RMT, Montel, exhaustion (Sard + retraction). This is the hardest
in-reach problem on the board and is unsolved by any system to date.

## Suggested milestone order (each independently valuable / upstreamable)

- **M1 Analytic core:** Montel/normal families → full Riemann Mapping Theorem.
- **M2 Green's functions** (Prop 9 + Lemma 8) on `Rado/` Perron.
- **M3 Biholomorphism** `K° ≃ D` (Thm 10 + RMT).
- **M4 Exhaustion** (Thm 12) — mostly independent, needs Sard.
- **M5 Assembly** (Lemma 13 + Thm 1 end) + dichotomy + `Diffeomorph` packaging.

## Potential source repos for the missing analytic pieces

Two prior AI-generated formalizations targeting **Abel's theorem / the Jacobian
of a compact Riemann surface** carry much of the complex-analytic machinery this
proof needs. Mine them "another time" rather than rebuilding from scratch:

- **https://github.com/rkirov/jacobian-claude** (Claude) and
  **https://github.com/rkirov/jacobian-fable** (Fable 5 rerun of the same, with a
  minimal blueprint summary).

Likely-reusable modules (names from the trees):
- `Dbar/` — the **∂̄ operator**, `CauchyKernel`, `SolveDisk`, `DiskAcyclic`,
  Wirtinger calculus, planar Cousin + partition of unity. This is the engine for
  constructing holomorphic functions / harmonic conjugates by solving ∂̄, i.e.
  the analytic heart of §2–3 (biholomorphism) and an alt route to Green's fn.
- `CanonicalForms/FormRemovableSingularity.lean` — **removable singularity for
  forms**, directly relevant to A–S **Lemma 8**.
- `Abel/LogPiece.lean`, `AbelWeak/PlanarLogBranch.lean` — **log branch / log
  singularity** handling, relevant to Green's-function pole (§1) and the period
  computation (§3).
- `Abel/AreaPairing.lean`, `AbelPairingStokes.lean`, `SerreFunctional.lean` —
  **Stokes / period pairings**, relevant to the `−2π` residue period in §3.
- `Cech/`, `DolbeaultComparison/`, `Dbar/DiskAcyclic` — cohomology-vanishing
  infrastructure (`H¹(disk)=0`), useful for period/exactness arguments.

⚠ **Caveats before reuse:**
- Both are **AI-generated and unreviewed** by the author ("I don't understand the
  math, and haven't reviewed any of this"). Audit soundness (`#print axioms`,
  `sorry` sweep) before trusting any lemma — do NOT import blindly.
- Different pins: `jacobian-claude` = Lean `v4.30.0`; `jacobian-fable` =
  `v4.30.0-rc2` + Mathlib `5483982…`. Our target is `v4.32.0-rc1` + Mathlib
  `360da6f`. Pieces need **porting across ~2 Mathlib versions**.
- They target compact surfaces (Jacobian/Abel); adapt statements to the
  noncompact `X` and open-disk setting here.

## Submission mechanics

Same as Radó: bundle a workspace `uniformization/` with `Submission.lean`
declaring the theorem, comparator restricts to `propext, Quot.sound,
Classical.choice`. See `generated/uniformization/` in `leanprover/lean-eval` and
`scripts/make_rado_submission.sh`.
