# Uniformization dev guide (agent playbook)

## Build / check
- Check a single file (ALWAYS use this while other agents may be running):
  `lake env lean Uniformization/<file>.lean`
- `lake build` only when no agents are running (shared lock; rebuilds mid-edit files).
- Beware bash cwd persisting (do not get stranded in `.lake/packages/mathlib`).
- Machine has 4 cores ⇒ at most 2 concurrent prover agents.
- Pin: Lean v4.32.2, Mathlib 905b9581 (browse `.lake/packages/mathlib/Mathlib/`).
- No `sorry`, no new axioms; audit with `#print axioms` (expect propext,
  Classical.choice, Quot.sound only).

## Ported RMT layer (`Uniformization/RMT/`, from mathlib PR #33505, axiom-audited)
- `Complex.exists_bijOn_unitBall_map_eq_zero` : RMT — `U` open, `IsSimplyConnected U`,
  `U ≠ univ`, `x₀ ∈ U` ⇒ ∃ f holomorphic on U, `BijOn f U (ball 0 1)`, `f x₀ = 0`.
- `Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn` : Hurwitz (injective limits).
- `Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn` : Hurwitz (zeros).
- `Complex.exists_branch_log` / `exists_branch_nthRoot` : branches on simply conn. sets.
- `Complex.equicontinuousAt_of_forall_norm_le`,
  `Complex.uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le` : Montel input
  (combine with `Topology/UniformSpace/Ascoli` from the pin).
- `Complex.UnitDisc.shift` : Möbius automorphisms of `𝔻`.

## Pin gotchas (learned the hard way)
- `convert` across `HasDerivAt/HasDerivWithinAt` produced by div/comp lemmas breaks on
  instance-path mismatches (`addCommGroup = ...` goals). Use `.congr_deriv` + `ring`/`simp`
  instead of `convert ... using 1`.
- `HasFDerivAtFilter.hasFDerivAt` doesn't exist at pin; `HasStrictDerivAt.hasDerivAt` does.
- Bare `mem_sdiff` is ambiguous (`Set` vs `Filter` both open) — qualify.
- `push_neg` deprecated → `push Not`.
- `LocPathConnectedSpace` → `LocallyPathConnectedSpace` (Mathlib 2026-06-21), and likewise
  `IsOpen.locPathConnectedSpace` / `ChartedSpace.locPathConnectedSpace` → `…locallyPathConnectedSpace`.
  The old names survive as `alias`es, but an `alias` of a class is a plain `def`, so an
  instance binder `[LocPathConnectedSpace X]` fails outright with "invalid binder annotation,
  type is not a class instance" — `haveI :` ascriptions still elaborate. Module
  `Mathlib.Topology.Connected.LocPathConnected` is now a `deprecated_module` shim for
  `…Connected.LocallyPathConnected`.
- Lean silently drops unused section hypotheses in statements — force with `include h`.

## Rado reuse layer
See `RADO_API.md` (full signatures). Highlights: `SurfaceHarmonicOn`/`SurfaceSubharmonicOn`,
`IsPerronFamily`/`perronSup` + `surfaceHarmonicOn_perronSup`, `poissonExtension` (Dirichlet
on disks), log-barriers in `Rado/Surface/Barriers.lean`, harmonic conjugates + étale space
in `Rado/Surface/Germs.lean` (`IsConjugate`, `ConjEtale`, `eval`), `HolomorphicOn` on X +
identity theorem in `Rado/Surface/Charts.lean`.

## Statements policy
Public statements of milestone-boundary lemmas are authored centrally (by the orchestrator)
and must not be changed by file agents; proof bodies are free.
