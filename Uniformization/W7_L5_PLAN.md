# W7 L5 micro-plan — proving `RegularSimplyConnected X`

Target (the ONLY thing left in W7), `Uniformization/Surface/Fill/Transfer.lean`:

```lean
def RegularSimplyConnected (X) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] : Prop :=
  ∀ V : Set X, IsOpen V → IsConnected V → IsCompact (closure V) →
    (frontier V).Nonempty → (∀ ξ ∈ frontier V, ExteriorDiskAt V ξ) →
    (∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x)) → IsSimplyConnected V
```

`exists_simply_connected_piece_of_regularSimplyConnected` already discharges the
frozen theorem from this predicate, feeding it the piece `V` from
`exists_regular_piece`. This document plans the proof of the predicate itself.
**No Lean proofs here — statements and sizing only.** Pin: Lean `v4.32.0-rc1`,
Mathlib `360da6f`.

---

## 0. Executive summary (read first)

1. **The macro plan (`W7_PLAN.md` L5–L9) is written against a geometry we do not
   have.** It assumes generic, transversal circle crossings giving a bicollared
   1-manifold frontier. The **delivered** `exists_regular_piece`
   (`Piece/Round.lean`) uses **compactness-only rounding**: circles may be
   tangent, may share arcs, the frontier is only known to lie on finitely many
   chart circles (`bcircles`), and multi-positive-circle points are *excluded*
   from the frontier while positive–negative crossings may sit on it. **`∂V` is
   therefore not known to be a topological 1-manifold.** This is the single fact
   that reshapes the whole plan.

2. **Every viable route needs a two-sided collar of `∂V`, and a collar needs a
   1-manifold frontier.** Crossing-parity (L6, the delivered `Parity.lean`
   engine) needs a phase map `τ : X → Circle` that is `1` off a collar and winds
   by `2π` across `∂V`; building `τ` requires a transversal normal coordinate,
   i.e. a collar. The A–S retraction (L8), inward push (L9), and any
   "collapse a complement end onto its frontier" step need the same. **Exterior
   disks give only outer, order-1 (tangent) contact on one side — not a two-sided
   collar — and at a cusp/tangency (allowed by compactness-only rounding) there
   is no continuous inward normal, so a partition-of-unity inward field is not
   assemblable either** (see §2). Hence the collar must come from the explicit
   circle-arc structure **after a genericity refinement**, not from
   `ExteriorDiskAt` alone.

3. **Consequence:** the honest route is the A–S retraction route (route (a)), but
   it is *gated* on first upgrading the delivered geometry to generic transversal
   crossings (`finite_tangency_radii`, deliberately **not** delivered — see
   `Piece/Generic.lean`'s scope-cut note) and re-rounding to a genuine 1-manifold
   frontier. Only then do the delivered engines (`Retraction.lean`,
   `Parity.lean`) and the `FrontierGlue` toolkit apply.

4. **Two-scale / adaptive-Green escape route is KILLED (§4):** it is circular
   (bounding a loop in a bigger piece `V'` still needs `IsSimplyConnected V'`),
   the downstream `exists_phi_of_green` genuinely needs simple connectivity of
   the **full** Green domain, and the adaptive level-set rescue either
   reintroduces Sard or re-assumes the simple connectivity it is trying to build.

5. **Recommendation:** strengthen `RegularSimplyConnected` to carry a
   `PieceData` witness + `Generic` (§3), redo the rounding generically, then run
   L5–L9. **This is not a 2–4 session task under any known route** (realistic:
   ~10–15 focused sessions). If the orchestrator wants to bound the risk, the
   structural fallback F3 (build `V` with a *smooth* regular-level-set boundary so
   the collar is free via the implicit function theorem) is the cheapest way to
   collapse L5+L9, at the cost of re-deriving `ExteriorDiskAt` on curved boundary.
   The confidence statement (§6) reflects this.

---

## 1. Assets actually in hand

Sorry-free, ready to consume:

* **`exists_regular_piece`** (`Piece/Round.lean`): `V = fill (connectedComponentIn (raw P) x₀)`
  for a `PieceData P` built by compactness-only rounding. Delivers every conjunct
  of the frozen theorem except `IsSimplyConnected V`, plus **no compact
  complement component** and `x₀ ∈ V`. Note: the `PieceData P` is *constructed
  inside the proof and not exposed in the statement*.
* **`isSimplyConnected_of_retract`** (`Fill/Retraction.lean`): a continuous
  `r : C(X,X)` with `r x ∈ A`, `r|A = id`, `[SimplyConnectedSpace X]` ⇒
  `IsSimplyConnected A`. This is the **L8 conclusion mechanism**. It applies to a
  *closed* `A` (typically `A = closure V`); it can NOT apply with `A = V` for open
  `V` with nonempty frontier (continuity at `ξ ∈ ∂V` forces `r ξ = ξ ∉ V`).
* **`lift_endpoint_eq_of_simplyConnected`** (`Fill/Parity.lean`): the **L6**
  winding-vanishes engine, `Circle.exp`-lifting; contrapositive gives the
  crossing-parity contradiction. Needs `τ : X → Circle`, a loop `δ`, and an
  explicit real lift `Λ` with `Λ 1 ≠ Λ 0`.
* **`HoleFill.lean`**: `fill`, `frontier_fill_subset` (filling shrinks frontier),
  `isCompact_closure_fill`, `isConnected_fill`, `not_isCompact_...compl_fill`,
  `connectedComponentIn_compl_fill`, `ExteriorDiskAt.fill/.anti`.
* **`Piece/Generic.lean`**: the countable-exclusion engine
  (`exists_radius_notMem`, `exists_radius_avoiding`, `finite_radii_through`).
  **Missing on purpose**: `finite_tangency_radii` (real-analytic critical values).
* **Moise templates** (namespace `LeanEval.…Moise`, must be copied/ported into
  our namespace — they are metric-target-free where it matters):
  - `FrontierGlue.lean`: `frontierGlue = Set.piecewise`,
    `continuous_frontierGlue_of_matches` (glue two continuous maps across an open
    frontier when `MatchesAtFrontier`), `range_frontierGlue`. **Directly reusable
    for L8** (no PL, no metric on target).
  - `NoRetraction.lean`: `no_retraction_closedUnitDisk` (the winding skeleton —
    our `Parity.lean` already abstracts it) and
    `exists_radial_retraction_to_frontier` (**planar** gauge/radial retraction of
    a punctured convex set onto its frontier — a template for the per-end collapse
    but only in a single chart).
  - `PolygonalJordan.lean` (4154 lines): planar PL collar/sector toolkit
    (`edgeTube`, `openAngularSector`, …). **PL-specific and LeanEval-namespaced**;
    usable only as a *pattern*, not an import.

Confirmed Mathlib tools (pin):

* `ContinuousMap.HomotopyEquiv.simplyConnectedSpace` (`…/SimplyConnected.lean:53`):
  `X ≃ₕ Y → [SimplyConnectedSpace Y] → SimplyConnectedSpace X`. **This is the
  clean L9 endgame**: a homotopy equivalence `↥V ≃ₕ ↥(closure V)` transports
  simple connectivity from the closed piece to the open one.
* `SimplyConnectedSpace.ofContractible` (instance) — if any stage is shown
  contractible.
* `isSimplyConnected_iff_exists_homotopy_refl_forall_mem` (used already).
* `Circle.isCoveringMap_exp`, `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`,
  `SimplyConnectedSpace.paths_homotopic`, Tietze
  (`ContinuousMap.exists_restrict_eq`), `SmoothPartitionOfUnity` /
  `exists_contMDiffMap_forall_mem_convex_of_local`.
* **No Sard** in Mathlib (only `MeasureTheory.Function.Jacobian` change-of-vars);
  `AnalyticOnNhd`/`IsolatedZeros` are present (grounds the countability fallback
  for `finite_tangency_radii`).

---

## 2. Collar strategy — decision

Three candidate sources for the collar; the decision is forced.

* **(i) From `ExteriorDiskAt` alone — REJECTED.** The exterior disk at `ξ` is an
  *open ball outside `V`, tangent at `ξ`*. It certifies one-sided, order-1
  contact only. It gives no coordinate on the `V`-side and no transversal normal.
  Two exterior disks at nearby frontier points need not align into a collar, and
  at a boundary cusp the tangent disks on either arc point in incompatible
  directions. Cannot define the `τ` normal coordinate. Insufficient.

* **(ii) Global inward field by partition of unity — REJECTED for this geometry.**
  `X` has `SmoothPartitionOfUnity` and
  `exists_contMDiffMap_forall_mem_convex_of_local`, so *if* every frontier point
  had a well-defined, locally consistent inward half-space one could glue a global
  inward-pushing homotopy. But under compactness-only rounding `∂V` can have
  cusps / tangential arc-meetings where **no continuous inward normal exists**;
  the local "push into `V`" data is not defined there, so the convex-combination
  hypothesis of the PoU gluing lemma fails. This route only becomes available
  *after* the genericity refinement makes `∂V` a 1-manifold — at which point the
  explicit radial collar (iii) is already in hand and cheaper.

* **(iii) From the explicit circle-arc structure, after a genericity refinement —
  CHOSEN.** After upgrading to transversal crossings (L5.0 below), `∂V` is a
  finite union of closed circular arcs meeting in pairs at transversal (convex,
  by rounding) corners — a compact topological 1-manifold. Each arc lies on ONE
  chart circle `circ d`; in `d`'s chart the **radial coordinate `‖e·−c‖ − ρ`** is
  a ready-made transversal normal coordinate with a two-sided collar
  `e⁻¹'(annulus)`. Corners are handled by the planar two-sector model
  (`openAngularSector` pattern). Conformality of transitions moves the radial
  normal of one chart into an overlapping chart. This is the macro plan's L5, now
  correctly *gated* on genericity.

**Decision: collar = radial coordinate in charts on a genericity-refined
1-manifold `∂V` (route iii).** This forces the refinement work L5.0.

---

## 3. What to strengthen in `RegularSimplyConnected` / `Transfer.lean`

The abstract predicate cannot be proved from its current hypotheses without
rebuilding the collar geometry from scratch each time. **Strengthen it to carry
the piece witness and its genericity**, and have `exists_regular_piece` expose
that witness. Two increments:

* **S-min (cheap, insufficient alone):** add
  `hcirc : ∃ (S : Finset (…circle…)), frontier V ⊆ ⋃ s ∈ S, s`. Already available
  from `PieceData.bcircles` — a two-line change to `exists_regular_piece` and the
  Transfer reduction. Useful but does **not** give the 1-manifold structure.

* **S-full (required for the chosen route):** replace the abstract quantifier by a
  witness form
  ```lean
  def RegularSimplyConnected (X) … : Prop :=
    ∀ (P : PieceData X) (x₀ : X),
      Generic P → x₀ ∈ raw P →
      IsSimplyConnected (fill (connectedComponentIn (raw P) x₀))
  ```
  (or keep the abstract `V`-form but add `∃ P, Generic P ∧ V = fill (connectedComponentIn (raw P) x₀)`
  as an extra hypothesis). Then:
  - **`Transfer.lean` reduction** must thread `P`, `Generic P`, and the defeq
    `V = fill (…)` out of a **generic** `exists_regular_piece`. Re-proving the
    reduction itself is cheap; the cost is in the next bullet.
  - **`exists_regular_piece` must be re-established with `Generic P`.** The
    delivered compactness-only rounding (`exists_rounding`) is replaced/augmented
    by a *generic* rounding that also secures transversality (needs
    `finite_tangency_radii`, L5.0). Everything downstream of rounding in the
    capstone (`exteriorDiskAt_raw`, the `fill`/component packaging) is reused
    verbatim — `Generic` is *additional* output, not a change to the existing
    conjuncts.

`Generic P` = the predicate of `W7_PLAN.md` §1.2 restricted to what L5–L6 use:
G1 transversal crossings (no two active circles tangent, in the conformal overlap
coordinate), G2 no triple points, G4 convex frontier corners. G2/G4 are already
"almost free" from the compactness rounding placement; G1 is the hard new content.

---

## 4. The two-scale / adaptive-Green escape — KILLED

Claim under test: avoid `IsSimplyConnected V` by giving downstream weaker
"two-scale" data (loops in `V` die in a bigger regular `V' ⊇` null-homotopy).

* **It is circular.** "`γ` (a loop in `V`) is null-homotopic in `V'`" requires
  `IsSimplyConnected V'`. The only *free* fact is that `γ`, as a loop in the
  simply connected `X`, is null-homotopic **in `X`**; pushing that null-homotopy
  into any `V'` is exactly the retraction problem again. No regular piece is known
  simply connected until we prove one is.

* **Downstream needs SC on the full Green domain.** `exists_phi_of_green`
  (`Phi.lean`) builds the global section `φ` by lifting a covering over **all of
  `U`**; the A–S injectivity/`|φ| → 1` argument needs `φ` on the entire Green
  domain `U`, so the section — hence `IsSimplyConnected U` — cannot live on a
  strict subdomain. (This is the previously-recorded failure of the two-scale
  attempt; re-confirmed here.)

* **Adaptive exhaustion does not rescue it.** Choosing the next compact to contain
  a superlevel set `Ω_c = {G > c}∋x₀` of the Green function `G := Green(V'ₙ)` does
  give open subdomains with `G = c` on their frontier, but: (a) `Ω_c` is
  simply connected only when `V'ₙ` already is (Green superlevel sets inherit, not
  create, simple connectivity), so it is circular; and (b) making the level set
  `{G=c}` a manifold for a *generic* `c` is **1-D Sard on `G`**, reintroducing the
  Sard the architecture forbids, and there is provably no forced gap between
  `min_{K} G` and `sup_{∂(intermediate)} G` in general. **Dead. Prove
  `IsSimplyConnected V` directly.**

---

## 5. Micro-lemma decomposition (the chosen route)

Files under `Uniformization/Surface/Fill/`. Sizes S/M/L/XL. `⇒` = depends on.
The route produces `IsSimplyConnected V` via:
`SimplyConnectedSpace X` ⟶(L5.5 retraction)⟶ `IsSimplyConnected (closure V)`
⟶(L5.6 collar homotopy equivalence + `HomotopyEquiv.simplyConnectedSpace`)⟶
`IsSimplyConnected V`.

### L5.0 — Generic rounding: transversal crossings ⇒ 1-manifold frontier `(XL, cost center)`
**File:** `Piece/Generic.lean` (finish) + `Piece/Round.lean` (generic variant).
**Out:** `finite_tangency_radii` (or its countability fallback) and a generic
`exists_rounding` producing `Generic P` with `∂V` a compact topological
1-submanifold: `∂V = ⋃` finitely many closed arcs, each `⊆` one `circ d`, meeting
pairwise only at transversal convex corners.
**Method:** for each pair of active circles in an overlap chart, tangency radii of
the pencil about `c` against the analytic image of the other circle are the
critical values of the real-analytic `g(x) = ‖x − c‖`; finite (or countable) by
`AnalyticOnNhd`/`IsolatedZeros`. Feed into `exists_radius_avoiding` (delivered) to
nudge radii off the bad set while preserving the `K`-cover margin.
**Risk:** real-analytic-on-a-compact-arc critical-value finiteness is thin in
Mathlib; the countability fallback (isolated zeros of `g'`) is the safe path but
still substantial. **This gates everything below.**

### L5.1 — Per-arc radial collar in a chart `(L)` ⇒ L5.0
**Out:** for each frontier arc `A ⊆ circ d`, an open `N_A ⊇ A`, a continuous
`s_A : N_A → (−1,1)` with `A = s_A⁻¹{0}`, `N_A ∩ V = s_A⁻¹(Ioo 0 1)` (or the
mirror for a negative circle), from the chart radial coordinate `‖e·−c‖ − ρ`
rescaled. **Method:** `Metric` sphere/annulus preimage under `e.symm`; the
`V`-side sign is fixed by pos/neg type (delivered `mem_odisk_iff` etc.).
**Risk:** low; pure chart computation.

### L5.2 — Corner collar (two-sector model) `(L)` ⇒ L5.0
**Out:** at each convex transversal corner `p = A ∩ A'`, a collar chart
identifying a punctured neighborhood with two sectors + a normal coordinate that
matches `s_A`, `s_{A'}` on the two incident arcs. **Method:** conformal image of
the planar `openAngularSector` two-sector picture (`PolygonalJordan` pattern),
using G4 convexity so `V` is the single reflex-free sector.
**Risk:** medium; the corner is where L5.1 collars are glued.

### L5.3 — Global two-sided collar of a frontier component `(L)` ⇒ L5.1,L5.2
**Out:** for each connected component `γ` of `∂V`, an open `N_γ ⊇ γ` and
continuous `s_γ : N_γ → (−1,1)`, `γ = s_γ⁻¹{0}`, sign-splitting `V`/complement,
by gluing L5.1/L5.2 pieces along `γ` (partition of unity on the compact 1-manifold
`γ`, or explicit finite arc/corner cover). **Risk:** medium; bookkeeping.

### L5.4 — Crossing parity: each complement end has connected frontier `(L)` ⇒ L5.3, Parity.lean
**Out:** for each (noncompact) component `Z` of `Vᶜ`, `frontier Z` is connected.
**Method:** the delivered `lift_endpoint_eq_of_simplyConnected`. Assume two
components `γ, γ'` of `frontier Z`; build `τ : X → Circle`, `τ = Circle.exp(2π λ(s_γ))`
on `N_γ` and `1` off it (`λ` monotone, `0`/`1` near the collar ends); build a loop
`δ` crossing `γ` exactly once (path-connectedness of `Z` and of `V`, then a
general-position wiggle transversal to the finitely many active circles — reuse
`exists_radius_avoiding`; injectivity of `δ` **not** needed); the explicit lift
`Λ = 2π λ(s_γ ∘ δ)` has `Λ1 − Λ0 = 2π ≠ 0`, contradicting the engine.
**Risk:** medium-high — the "crosses `γ` once" bookkeeping; collar `s_γ` (L5.3)
makes "transversal" = "`s_γ∘δ` changes sign once".

### L5.5 — A–S retraction ⇒ `IsSimplyConnected (closure V)` `(L)` ⇒ L5.3,L5.4, FrontierGlue, Retraction.lean
**Out:** `r : C(X,X)`, `r|closure V = id`, `r x ∈ closure V`, then
`isSimplyConnected_of_retract` gives `IsSimplyConnected (closure V)`.
**Method:** on `closure V`, identity; on each noncompact end `Z`, collapse to its
(now connected, L5.4) frontier `γ_Z` via a Tietze map `Ψ_Z : Z → γ_Z` that is
`id` on `γ_Z` (Tietze `ContinuousMap.exists_restrict_eq` on `Z` with boundary data
along an escaping ray, or the `exists_radial_retraction_to_frontier` planar
template lifted through the end's collar); glue by `frontierGlue` /
`continuous_frontierGlue_of_matches` (the `MatchesAtFrontier` obligation is
immediate: `Ψ_Z = id` on `γ_Z`). Escaping ray in `Z` from local compactness (no
`SecondCountableTopology`!) — sub-lemma **L5.5a `(M)`**.
**Risk:** high — assembling `Ψ_Z` and the ray; largest classical-topology step.

### L5.6 — Inner-collar homotopy equivalence ⇒ `IsSimplyConnected V` `(XL)` ⇒ L5.3,L5.5
**Out:** `IsSimplyConnected V` from `IsSimplyConnected (closure V)`.
**Method:** the inner half `s_γ ∈ [0,ε)` of the L5.3 collars gives an inward push
`F : I × closure V → closure V`, `F 0 = id`, `F 1(closure V) ⊆ V`, `F t(V) ⊆ V`;
package as `↥V ≃ₕ ↥(closure V)` and finish with **`ContinuousMap.HomotopyEquiv.simplyConnectedSpace`**.
**Method-glue:** the global inward push is a PoU combination of per-arc radial
pushes (`SmoothPartitionOfUnity` subordinate to the arc/corner cover).
**Risk:** highest single step — global inward push across corners; this is the
open↔closed transfer the macro plan flags as unavoidable (D4/§4).

### L5.7 — Assemble the strengthened predicate `(S/M)` ⇒ L5.5,L5.6
Package L5.6 as `RegularSimplyConnected X` (S-full form, §3) and repair
`Transfer.lean`'s reduction to feed the generic `exists_regular_piece` witness.

**Dependency DAG:**
```
L5.0 ─┬─> L5.1 ─┐
      └─> L5.2 ─┴─> L5.3 ─┬─> L5.4 ─┐
                          │         ├─> L5.5 ─> L5.6 ─> L5.7
                    L5.5a ┘─────────┘
```

---

## 6. Fallbacks and the decision the orchestrator faces

* **F1 (collar weakening, applies to L5.1–L5.3).** L5.4/L5.5 only need a single
  continuous signed coordinate `s_γ` with `γ = s_γ⁻¹{0}` and the sign split — not
  a product bicollar `γ×(−1,1)`. Build `s_γ` as a chart-glued signed
  radial/`infDist` function; skip the manifold-atlas claim. Roughly halves L5.3.

* **F2 (drop injectivity everywhere).** The winding argument (L5.4) and the glue
  (L5.5) never need embedded/simple `δ` or embedded rays; keep all maps
  merely continuous. Already folded into the statements above.

* **F3 (structural smooth boundary — the real de-risking lever, orchestrator's
  call).** Replace the disk-minus-disk `V` by `V = {f > 0}` for a smooth
  `f : X → ℝ` (mollified max of chart bumps) with `0` a regular value. Then:
  - `∂V = f⁻¹{0}` is a smooth compact 1-manifold with a two-sided collar **free**
    from the implicit function theorem (`f` itself is the normal coordinate) —
    **L5.1–L5.3 collapse to near-nothing, and L5.6's inner push is the collar
    flow, trivializing the open↔closed transfer.**
  - Cost moved: (a) securing "`0` is a regular value" is 1-D Sard on `f`
    (critical values of a `C¹` map `2-mfd → ℝ` have measure zero) — **not in
    Mathlib**, must be built or replaced by an explicit genericity argument on the
    bump heights; (b) **re-deriving `ExteriorDiskAt` on the curved smooth boundary**
    (the delivered proof is disk-specific), needing bounded curvature / a one-sided
    supporting-disk lemma. This throws away the delivered `exteriorDiskAt_raw`.
  - **Verdict:** F3 trades the L5.0 genericity + L5.1–L5.3 + L5.6 analytic burden
    for a smaller-but-still-real (1-D Sard) + (smooth-boundary `ExteriorDiskAt`)
    burden. Worth it **only if** L5.0 or L5.6 stalls. Keep the disk `V` (route iii)
    as primary because `ExteriorDiskAt` is already delivered for it.

* **F4 (single-chart cells — de-risks L5.0/L5.4).** Rebuild L1 (`Cover.lean`) as a
  *tree of disks whose overlaps live in single charts* (`W7_PLAN.md` §4). Then
  every arc-cycle stays in one chart and L5.1–L5.4 reduce to the planar
  `PolygonalJordan` toolkit under one conformal chart. Costs a disciplined
  rewrite of `Cover.lean` but removes all cross-chart collar bookkeeping.

---

## 7. Ten-line summary + confidence

1. `RegularSimplyConnected X` is the only W7 gap; the frozen theorem already
   reduces to it (`Transfer.lean`, sorry-free).
2. **Decisive finding:** the delivered piece uses *compactness-only rounding*, so
   `∂V` is **not** a known 1-manifold — the macro plan's collar-based L5–L9 do not
   apply as written.
3. Collar decision: must come from the **circle-arc structure after a genericity
   refinement**; `ExteriorDiskAt`-only and PoU-inward-field are both insufficient
   without that refinement (cusps/tangencies have no inward normal).
4. Route chosen: A–S retraction ⇒ `IsSimplyConnected (closure V)` (delivered
   `Retraction.lean` + `Parity.lean` + `FrontierGlue`), then inner-collar
   homotopy equivalence ⇒ open `V` via the confirmed
   `HomotopyEquiv.simplyConnectedSpace`.
5. Predicate strengthening (§3): carry `PieceData P` + `Generic P`; requires a
   **generic re-rounding** of `exists_regular_piece` (new `finite_tangency_radii`).
6. Two-scale / adaptive-Green escape is **killed** (§4): circular, needs SC on the
   full Green domain, adaptive level sets reintroduce Sard.
7. Cost centers: L5.0 (generic rounding / analytic tangency finiteness) and L5.6
   (open↔closed inner-collar transfer); L5.4/L5.5 are medium given the engines.
8. Confirmed tooling: `HomotopyEquiv.simplyConnectedSpace`, `ofContractible`,
   `Circle.isCoveringMap_exp` lifting, Tietze, `SmoothPartitionOfUnity`; **no Sard
   in Mathlib** (grounds both the L5.0 fallback and the F3 caveat).
9. Real-cost de-risking lever: **F3** (smooth regular-level-set boundary ⇒ free
   collar) if L5.0/L5.6 stall; **F4** (single-chart tree cells) to localize L5.1–4.
10. **Confidence that the chosen route closes in ~2–4 prover-agent sessions:
    LOW.** Honest total is ~10–15 focused sessions (L5.0 and L5.6 alone are
    multi-session). 2–4 sessions is realistic only for a *sub-goal*
    (e.g. L5.1–L5.3 collar given L5.0, or L5.4 given collars), or if F3/F4 sharply
    shrink the geometry. Recommend the orchestrator either commit to the full
    multi-session route or green-light the F3 structural reconstruction before
    investing in L5.0.

---

## ORCHESTRATOR DECISION (2026-07-16): F3 adopted, in harmonic form

Route F3 is adopted with `f` := the **Perron/Dirichlet harmonic function**
(via the proven `exists_dirichlet_solution`) on an annular region between an
inner regular piece around `K` and an outer regular piece (both from
`exists_regular_piece`), boundary data 0 / 1. Then:
- `∂f` is holomorphic in charts, `f` nonconstant per component (max principle)
  ⇒ critical points isolated ⇒ **critical values countable — regular values
  exist with NO Sard** (the analyticity trick, same spirit as the tangency-radii
  countability).
- `V' := inner piece ∪ (component of {f > c})` for a regular value `c`:
  real-analytic corner-free boundary; `ExteriorDiskAt` from bounded curvature
  (quantitative tangent disks); collar from the implicit function theorem /
  the local biholomorphism `F = f + i·f̃` (conjugate exists locally by
  `Rado.exists_conjugate`), which maps the level curve into a straight line —
  arc-tracing without corners; L9 transfer eased by the genuine collar.
- Parity engine (`Fill/Parity.lean`) still supplies per-end frontier
  connectivity; Retraction engine unchanged.
Execution order: (F3.a) harmonic-level-set piece construction + regular value
selection; (F3.b) level-curve local structure via `F = f + i f̃`; (F3.c)
collar + retraction + transfer.
