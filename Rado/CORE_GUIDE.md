# Prover guide: Rado/Surface/Core.lean

Working rules (also see PLAN.md):

- Edit ONLY `Rado/Surface/Core.lean`. Never touch other files (siblings are edited concurrently by other agents).
- Only replace `sorry` bodies; never change the statement/name/signature of an existing declaration. New private helper lemmas inside the file are fine.
- Type-check ONLY with `cd /home/rado/jordan_pick && lake env lean Rado/Surface/Core.lean` (~60–90s; write substantial chunks between checks). NEVER run plain `lake build`.
- Imported Rado files may contain sorries; rely on their statements.
- If a statement is unprovable as stated, leave it sorried, add a corrected variant under a new name, prove that, and flag it.
- Math sources: `reference/rado/anghel-stan.txt` (Perron proof: Appendix A, ~lines 640–720), `reference/rado/rainer.txt` (§22–23).

Priority order and per-item guidance:

## 1. SubMeanLocalOn block (3 sorries)

`eqOn_const_of_isMaxOn` / `le_of_frontier_le`: adapt the finished proofs of
`SubMeanOn.eqOn_const_of_isMaxOn` / `SubMeanOn.le_of_frontier_le` in
`Rado/Complex/SubMean.lean` (read them). Only change: where they use circles of
every radius `< ε`, intersect with the small radii from `submean_small`
(`∀ᶠ r in 𝓝[>] 0` gives an interval `(0, ρ)`; use `min`).

`subMeanOn` (the bridge): given `closedBall c R ⊆ s`, let
`P := poissonExtension g c R` (API in `Rado/Complex/Dirichlet.lean`). Show
`g ≤ P` on the closed ball by applying the local `le_of_frontier_le` on
`U := ball c R` to `g - P` (locally submean: `g` local + `P` `MeanEqOn` from
`HarmonicOnNhd.meanEqOn`; continuity on `closure_ball`; `frontier_ball` =
sphere where `g - P = 0` by `poissonExtension_eqOn_sphere`). Then
`g c ≤ P c = circleAverage P c R = circleAverage g c R`:
`HarmonicContOnCl.circleAverage_eq` (Mathlib `Analysis/Complex/Harmonic/MeanValue.lean:50`,
build `HarmonicContOnCl` via `HarmonicContOnCl.mk_ball`,
`Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean:62`) plus a
circle-average congruence on the sphere (integrands agree at `circleMap` points
via `circleMap_mem_sphere` + `poissonExtension_eqOn_sphere`; use
`intervalIntegral.integral_congr` or an existing congr lemma in
`Mathlib/MeasureTheory/Integral/CircleAverage.lean`).

## 2. SurfaceSubharmonicOn.of_locally

For each chart `e`, the rep `g ∘ e.symm` is `SubMeanLocalOn` on
`chartImage e s`: each `w ∈ chartImage e s` comes from `x` in some local `V`;
`SubMeanOn` on the open `chartImage e V ∋ w` supplies all small circles.
Conclude with `SubMeanLocalOn.subMeanOn`.

## 3. surfaceReplace lemmas (4 sorries)

Notation: `D := e.symm '' closedBall c r`, `hd : IsReplaceDisk e c r s`.

- `le_surfaceReplace`: for `x ∈ D`: `x ∈ e.source` (`map_target`),
  `e x ∈ closedBall`; dite-true branch. `closedBall c r ⊆ chartImage e s`
  (for `w ∈ closedBall`: `w = e (e.symm w)`, `e.symm w ∈ s` by
  `hd.preimage_subset`). Apply `SubMeanOn.le_poissonExtension_on` to
  `hg.subMeanOn e hd.mem_atlas`; rewrite `g x = (g ∘ e.symm) (e x)` via
  `e.left_inv`. For `x ∉ D`: `surfaceReplace_eqOn_compl`.
- `surfaceReplace_surfaceHarmonicOn`: via `SurfaceHarmonicOn.of_chartwise`
  with chart `e`: near `w ∈ ball c r`, the rep `surfaceReplace ∘ e.symm`
  agrees with `poissonExtension (g ∘ e.symm) c r` (on the open preimage the
  dite takes the true branch and `e (e.symm w') = w'`); then
  `poissonExtension_harmonicOnNhd` + `harmonicAt_congr_nhds`.
- `surfaceReplace_mem_Icc`: split `x ∈ D` (`poissonExtension_mem_Icc`, sphere
  data are `g`-values at points of `s`) / `x ∉ D` (equals `g`).
- `surfaceReplace_surfaceSubharmonicOn` (Anghel–Stan Remark 4): first prove
  continuity on `s` (interior: harmonic; exterior: equals `g` on a nbhd —
  NOTE this section has no `[T2Space X]`, so closedness of the compact `D`
  is not free. `D` IS closed inside the subspace `e.source` (homeo image of
  the closed `closedBall ∩ e.target`); that suffices for nbhds of exterior
  points in `e.source`; points outside `e.source`... if you conclude T2 is
  genuinely needed, prove primed variants with `[T2Space X]` under new names,
  leave originals sorried, and flag — downstream (config) has T2.
  At circle points `p`: for every chart `e'` and small circles around `e' p`:
  `(surfaceReplace g) p = g p ≤ circleAverage (g ∘ e'.symm) ≤
  circleAverage ((surfaceReplace g) ∘ e'.symm)` using `le_surfaceReplace` +
  `circleAverage_mono`. That gives `SubMeanLocalOn` per chart; bridge (1) +
  `of_locally` (2) assemble.

## 4. IsPerronFamily.surfaceHarmonicOn_perronSup (Perron's principle) — deepest

Follow Anghel–Stan Appendix A. Use `SurfaceHarmonicOn.of_chartwise`: fix
`x ∈ s`, chart at `x`, `closedBall (e x) r ⊆ chartImage e s`. Dense sequence
`(z_j)` in the ball (`exists_countable_dense`/`denseSeq`). Build an increasing
sequence `h_n ∈ 𝓕` harmonic on the disk preimage: max with members nearly
attaining `perronSup` at `z_1..z_n`, include `h_{n-1}` in the max, then
`surfaceReplace` on the disk (stays in `𝓕` by `max_mem`/`replace_mem`;
harmonic inside by `surfaceReplace_surfaceHarmonicOn`; `≥ h_{n-1}` by
`le_surfaceReplace`). `w := ⨆ n, h_n` pointwise (values in `[0,1]`).
(i) `w = perronSup 𝓕` at the `z_j`-preimages by construction.
(ii) `w` harmonic on the disk — monotone limit of harmonic. Route (a) Harnack:
for `n ≥ m`, `h_n - h_m ≥ 0` harmonic; Poisson representation
(`HarmonicContOnCl.circleAverage_poissonKernel_smul`,
`Analysis/Complex/Harmonic/Poisson.lean`) + two-sided kernel bounds
(`re_herglotzRieszKernel_le` / `le_re_herglotzRieszKernel` via
`poissonKernel_eq_re_herglotzRieszKernel`) give Harnack on sub-disks ⇒
uniformly Cauchy on compacts ⇒ uniform limit; uniform limits of harmonic are
harmonic (pass the representation/mean value to the limit; then
`MeanEqOn.harmonicOnNhd`). Route (b): A–S's dominated-convergence argument.
Build private helpers (Harnack inequality, uniform-limit-harmonic) first.
(iii) `w = perronSup` on the whole disk: `w ≤ perronSup` via `le_perronSup`;
for `≥`: given `g ∈ 𝓕`, rebuild a second sequence including `g`; its limit
`w'` is harmonic, `w ≤ w' ≤ perronSup`, `w = w'` on the dense set (both equal
`perronSup` there), two continuous (harmonic) functions equal on a dense
subset of the disk are equal ⇒ `g ≤ w' = w` ⇒ `perronSup ≤ w`.

## 5. Config section (6 sorries; `he`, `hb`, and per-theorem `[T2Space X]` available)

- `isOpen_configY`: `K_i := e.symm '' closedBall (±4) 1` compact (as in
  `IsReplaceDisk.compact_preimage`; `closedBall (±4) 1 ⊆ ball 0 8 ⊆ e.target`)
  ⇒ closed (T2) ⇒ complement open.
- `witness_mem_configY` (do this before the others): `w₁ := 4 + (2:ℂ)^((1:ℂ)/4)`:
  `‖(2:ℂ)^((1:ℂ)/4)‖ = (2:ℝ)^(1/4 : ℝ)` (`Complex.norm_cpow_eq_rpow_re_of_pos`),
  and `1 < 2^(1/4) < 2` (rpow monotonicity). `w₁ ∈ ball 0 8 ⊆ e.target`;
  `e.symm w₁ ∉ e.symm '' closedBall (±4) 1` by `e.symm` injectivity on the
  target (`e.injOn`/`left_inv`-based) + `dist w₁ (±4) > 1`.
- `isConnected_configY`: `P := e.symm '' (ball 0 8 \ (closedBall (-4) 1 ∪ closedBall 4 1))`:
  open, path-connected (`isPathConnected_ball_diff_two_disks` from
  `Rado/Complex/PlanarConnected.lean`, image under continuous injective
  `e.symm` via `IsPathConnected.image`), `P ⊆ configY e`, nonempty.
  KEY geometric fact: every point of `K₀ ∪ K₁` has arbitrarily small nbhds `N`
  (chart preimages of balls inside `ball 0 8`) with `N ∩ configY ⊆ P`
  (a ball inside `ball 0 8` minus the two disks is inside
  `ball 0 8 \ disks`). Suppose `Y ⊆ A ∪ B`, `A`,`B` open disjoint, `P ⊆ A`
  wlog; show `T := B ∩ Y` is clopen in `X` (open ✓; closed: limit points in
  `Y` stay in `T` by disjointness from open `A`; limit points in `K_i` are
  impossible since their small nbhds meet `Y` only inside `P ⊆ A`); `T ≠ X`,
  `ConnectedSpace X` ⇒ `T = ∅`. Use `isPreconnected_iff_subset_of_disjoint`
  and `IsClopen.eq_univ`/`eq_empty`.
- `isPerronFamily_configFamily`: nonempty: the zero function
  (`SubMeanOn.const`, `continuousOn_const`). `max_mem`:
  `SurfaceSubharmonicOn.max`, `ContinuousOn.sup`, arithmetic. `replace_mem`:
  subharmonic by (3); the disk `D ⊆ Y` is compact hence closed (T2 ✓ here),
  so the replacement equals `g` on a nbhd of `closure Y \ Y`; continuity on
  `closure Y` by gluing; Icc via `surfaceReplace_mem_Icc` + equality outside;
  boundary condition unchanged.
- `perronSup_ge_witness` (lower barrier):
  `β x := if x ∈ e.source then max 0 ((Real.log 2 - Real.log ‖e x - 4‖) / Real.log 2) else 0`.
  Show `β ∈ configFamily e` and `β (e.symm w₁) = 3/4`
  (`Real.log_rpow`; `log 2 ≠ 0`), then `IsPerronFamily.le_perronSup`.
  Subharmonicity via `of_locally`: near points with `‖e x - 4‖ < 5/2`:
  `β = max 0 (harmonic)` (harmonicity of `w ↦ log ‖w - 4‖` away from `4`:
  grep `Mathlib/Analysis/Complex/Harmonic/Constructions.lean` for the log-norm
  harmonic lemma; wrap with `SurfaceHarmonicOn.of_chartwise` through chart `e`,
  then `.surfaceSubharmonicOn` and `SurfaceSubharmonicOn.max` with the
  constant `0`); near points with `‖e x - 4‖ > 2` or off `e.source`: `β ≡ 0`
  locally (the set `e.symm '' closedBall 4 2` is compact hence closed (T2);
  off it, if `x ∈ e.source` then the log term is `< 0` so `max` gives `0`,
  and off `e.source` it is `0` by definition). Overlap consistent
  (`max 0 h = 0` when `‖·‖ ≥ 2`). Continuity on `closure Y`: same pieces.
  Boundary: on `K₀`-side `‖e x - 4‖ ≥ 7` ⇒ `β = 0`. Bounds: on `closure Y`,
  `‖e x - 4‖ ≥ 1` ⇒ value in `[0,1]`.
- `perronSup_le_witness` (upper barrier):
  `γ w := 1 - (Real.log 2 - Real.log ‖w + 4‖) / Real.log 2` on the open
  annulus `A := {w | 1 < ‖w + 4‖ ∧ ‖w + 4‖ < 2}`. For every `g ∈ configFamily`:
  `(g ∘ e.symm) - γ` is `SubMeanOn` on `A` (`A ⊆ chartImage e (configY e)`:
  `‖w‖ < 6 < 8` and outside both disks; `γ` harmonic on `A` (−4 ∉ A) ⇒
  `MeanEqOn` ⇒ `SubMeanOn.add_meanEq` with `MeanEqOn.neg`). `A` bounded;
  continuity on `closure A` ⊆ closed annulus ⊆ `e.symm ⁻¹`-image of
  `closure (configY e)` (inner circle points are limits of radially-outward
  points of `Y`). `frontier A ⊆ {‖w+4‖ = 1} ∪ {‖w+4‖ = 2}`: `A = f ⁻¹' (Ioo 1 2)`
  for `f w := ‖w + 4‖` continuous: `f ⁻¹' Ioo ⊆ interior A`,
  `closure A ⊆ f ⁻¹' Icc`. Boundary values: inner circle: `γ = 0`, `g ≤ 0`
  (family boundary condition; the point is in `closure Y ∩ K₀`); outer:
  `γ = 1 ≥ g`. `SubMeanOn.le_of_frontier_le` ⇒ `g ∘ e.symm ≤ γ` on
  `closure A ∋ w₀ := -4 + 2^(1/4)`; `γ w₀ = 1/4`; finish with
  `IsPerronFamily.perronSup_le`.

## 6. Étale section (11 sorries) + assembly (4 sorries)

Key generic facts: germ equality ↔ `=ᶠ[𝓝 y]` (`Filter.Germ` coe lemmas);
`germValue ↑F = F y` (by `rfl`-ish `liftOn` simp); the germ-agreement set
`{z | F =ᶠ[𝓝 z] G}` is open.

LOCAL TRIVIALITY (use everywhere): for a basic sheet datum `(V, F)` and any
étale point `q` with `proj q ∈ V`: `q`'s own conjugate datum `(W, G)` and
`IsConjugate.eventuallyEq_add_const` give `t` with `G =ᶠ F + tI` at the base
point, so `q ∈ sheet V (fun z => F z + t*I)`, and `F + tI` is a conjugate on
`V` (`IsConjugate.add_const_mul_I`).

THE SECTION MAP (use everywhere): for a basic sheet `S = sheet V F`, define
`σ : V → ConjEtale`, `σ y := ⟨⟨y, ↑F⟩, …⟩`. `σ` is continuous
(`σ ⁻¹' (sheet W G)` is the open germ-agreement locus intersected with
`V ∩ W`), open (`σ '' O = proj ⁻¹' O ∩ S`), inverse to `proj|S`. All local
properties transfer along it.

- `isTopologicalBasis_basicSets`: construct the `IsTopologicalBasis` structure
  directly (fields: point-refinement of intersections, `sUnion_eq`,
  `eq_generateFrom`). Coverage: every `q` has `(V, F)`; refine `V` to
  `connectedComponentIn V (proj q)` (open: `LocallyConnectedSpace X` via
  `ChartedSpace.locPathConnectedSpace` as `haveI`; conjugates restrict).
  Intersections: germs agree at the common base ⇒ agree on an open set `O`;
  refine to `connectedComponentIn (V₁ ∩ V₂ ∩ O) y`.
- `continuous_proj`/`isOpenMap_proj`/`injOn_proj_sheet`: as designed
  (images of sheets are their `V`s; preimages of opens are unions of refined
  sheets; injectivity by `Subtype.ext`/`Sigma` equality).
- `t2Space`: different base points: separate via `proj` preimages (T2Space X).
  Same base: two sheets over a common `connectedComponentIn (V ∩ V') y`; if
  they met, `HolomorphicOn.eqOn_of_eventuallyEq` (identity theorem, Charts)
  would force equal germs at `y`.
- `exists_mk`: from `exists_conjugate`.
- local properties (`locallyCompactSpace`, `locallyConnectedSpace`,
  `locally_secondCountable`): transfer along `σ` from `X`'s properties
  (`ChartedSpace.locallyCompactSpace ℂ X`, `locPathConnectedSpace`,
  `OpenPartialHomeomorph.secondCountableTopology_source` + hereditary
  second countability along embeddings — see the pattern in
  `Rado/Topology/PoincareVolterra.lean` (`secondCountableTopology_of_subset`)).
- `continuous_eval`: on a sheet, `eval = F ∘ proj`; congruence on an open nbhd.
- `eval_discrete_fibers`: at `q` over sheet `(V, F)`, `V` preconnected. If the
  chart rep of `F - eval q` is eventually zero at the base: `u` locally
  constant ⇒ `SurfaceHarmonicOn.eqOn_const_of_locallyConstant` ⇒ `u` constant
  on `Y` ⇒ contradicts `hne`. Otherwise
  `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
  (`Mathlib/Analysis/Analytic/IsolatedZeros.lean`) gives a punctured nbhd
  where `F ≠ eval q`; pull back and refine the sheet.
- `surjOn_proj_connectedComponent`: image is open (component open — étale is
  locally connected via the theorem, as `haveI` — plus `isOpenMap_proj`) and
  closed in `Y` (a boundary point has a trivializing preconnected `V` by
  `exists_conjugate`; a sheet over `V` meets the component, sheets over
  preconnected `V` are connected (`σ` image) ⇒ contained in the component ⇒
  `V ⊆` image). Relative clopen + `hYc` ⇒ image `= Y`.
- `exists_config_chart`: `chartAt x₀`; ball in the open target; affine
  normalization via `affine_trans_mem_riemannAtlas` with `a := 8/ρ`,
  `b := -(8/ρ) * c₀`; recover the target from
  `OpenPartialHomeomorph.image_source_eq_target` + the value equation
  (add a helper if the ∃-form is too weak — do NOT change the Charts
  statement).
- `locally_secondCountable_subtype`: preimage of the second-countable open;
  hereditary second countability along the inclusion embedding (pattern in
  PoincareVolterra.lean).
- `secondCountable_configY`: the full assembly per PLAN.md step 8 — set
  `Y := configY e`, `u := perronSup (configFamily e)`; instances via `haveI`
  (X: locally compact/connected; étale: `t2Space`, `locallyCompactSpace`,
  `locallyConnectedSpace`); `q₀` over the witness; `C := connectedComponent q₀`
  (open: `isOpen_connectedComponent`; `ConnectedSpace ↥C` via
  `Subtype.connectedSpace isConnected_connectedComponent`; `↥C` locally
  compact/connected as an open subspace — grep for `IsOpen.locallyCompactSpace`
  and the locally-connected analogue, prove by hand if missing);
  `poincare_volterra` with `eval ∘ Subtype.val`; descent
  `g : ↥C → ↥Y := Set.codRestrict …` continuous, surjective
  (`surjOn_proj_connectedComponent`), open (unfold `isOpen_induced_iff`),
  then `(IsOpenMap.isQuotientMap …).secondCountableTopology`
  (`Mathlib/Topology/Bases.lean:1120`).
- `secondCountableTopology_of_riemannSurface`: `rcases isEmpty_or_nonempty X`
  (empty case: find/prove the trivial instance); two-set open cover
  `{configY e, e.symm '' ball 0 8}` = univ (`closedBall (±4) 1 ⊆ ball 0 8`),
  both second countable (`secondCountable_configY`; chart piece: subset of
  `e.source`, `OpenPartialHomeomorph.secondCountableTopology_source` +
  hereditary), finish with `Rado.secondCountableTopology_of_countable_setCover`.

Do NOT touch `Rado/Main.lean`; the orchestrator wires the final theorem.
