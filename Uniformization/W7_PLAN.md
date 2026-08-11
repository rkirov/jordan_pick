# W7 proof plan — `exists_simply_connected_piece`

Target (frozen, `Uniformization/Surface/Fill.lean`):

```lean
theorem exists_simply_connected_piece [T2Space X] [ConnectedSpace X]
    [SimplyConnectedSpace X] (hnc : ¬ CompactSpace X)
    {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
      IsSimplyConnected V ∧ (frontier V).Nonempty ∧
      ∀ ξ ∈ frontier V, ExteriorDiskAt V ξ
```

`X` is a Riemann surface: `[TopologicalSpace X] [ChartedSpace ℂ X]
[IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]`. Pin: Lean `v4.33.0`, Mathlib
`db584cd6`. This document is a specification for prover agents. It does **not**
contain Lean proofs.

Free structural facts we get from the instances (cite in every file):
`ChartedSpace ℂ X` ⇒ `LocallyCompactSpace X`, `LocallyConnectedSpace X`,
`LocPathConnectedSpace X` (`ChartedSpace.locallyCompactSpace`,
`.locallyConnectedSpace`, `.locPathConnectedSpace`, since `ℂ` has all three).
`ConnectedSpace X` + `LocPathConnectedSpace X` ⇒ `PathConnectedSpace X`.
Transition maps of `riemannAtlas X` are **holomorphic hence conformal**
(`Rado/Surface/Charts.lean`) — angle-preservation is used repeatedly below.

---

## 0. Executive decisions (read first)

- **D1 (geometry).** A piece is a **boolean disk region**: a finite set of
  *positive* closed chart disks (whose interiors' union covers and connects `K`)
  minus a finite set of *negative* "corner-rounding" chart disks. Pure unions of
  disks are **rejected** — see the reflex-corner finding D2. `V` is the interior
  of (positive union minus negative disks), then **hole-filled**.
- **D2 (the reflex-corner finding — the single most important design fact).**
  At a transversal crossing `p` of two boundary circles of a *union* of disks,
  `V` occupies **3 of the 4 local sectors**; the complement is a single sector of
  angle `< π`. Because transition maps are conformal, this angle is
  chart-independent. An exterior disk needs an open round ball tangent at `p`
  whose interior misses `V`; such a ball subtends a half-plane (`π`) of directions
  and cannot fit inside a `< π` sector. **Therefore `ExteriorDiskAt V p` is FALSE
  at every exposed union-crossing.** A union-of-disks piece cannot satisfy the
  frozen theorem's last conjunct. This is why D1 subtracts small disks to round
  each exposed reflex corner into a smooth concave arc flanked by two *convex*
  corners, all of which admit exterior disks.
- **D3 (single-chart boundary localisation).** Every frontier arc lies on the
  boundary circle of exactly one disk (positive or negative), and its exterior
  disk is always exhibited **in that disk's own chart**. No frontier point's
  regularity witness ever needs a cross-chart construction. "Generic position"
  is imposed and used entirely inside single charts / conformal chart overlaps.
- **D4 (simple connectivity route).** Use the **A–S retraction to the closed
  piece**: build `r : X → closure V`, identity on `closure V`, collapsing each
  unbounded complement end onto its (connected) frontier arc-cycle; conclude
  `SimplyConnectedSpace (closure V)` by the retract argument. Then transfer to the
  *open* `V` by an **inner-collar homotopy equivalence** (Step L9). We deliberately
  do **not** attempt a direct "loop null-homotopic in `V`" argument: §4 shows it
  cannot avoid the same collar, so it buys nothing.
- **D5 (no Jordan curve theorem, no de Rham, no Sard).** Frontier connectivity of
  complement ends is proved by **crossing parity via a map `τ : X → Circle`** and
  `Circle.isCoveringMap_exp` lifting (the `Moise/NoRetraction.lean` pattern),
  never by Jordan separation.

---

## 1. Geometry, data structure, and genericity

### 1.1 The `PieceData` structure

Work relative to `riemannAtlas X`. A **chart disk** is a triple `(e, c, ρ)` with
`e ∈ riemannAtlas X`, `c : ℂ`, `ρ : ℝ`, `0 < ρ`, `closedBall c ρ ⊆ e.target`.
Its **carrier** in `X` is `disk e c ρ := e ⁻¹' closedBall c ρ` (⊆ `e.source`),
open carrier `odisk e c ρ := e ⁻¹' ball c ρ`, boundary circle
`circ e c ρ := e ⁻¹' sphere c ρ`. All three are well-defined subsets of `X`;
`odisk` is open, `disk` compact (`e` is a homeomorphism onto `e.target ⊇
closedBall`, and `closedBall` compact), `circ = frontier (odisk)` inside `e.source`.

```
structure PieceData (X) [ChartedSpace ℂ X] where
  pos : Finset ChartDisk         -- included disks
  neg : Finset ChartDisk         -- corner-rounding disks to subtract
```

Derived sets:

- `raw P    := (⋃ d ∈ P.pos, odisk d) \ (⋃ d ∈ P.neg, disk d)`   (open)
- `bcircles P := (⋃ d ∈ P.pos, circ d) ∪ (⋃ d ∈ P.neg, circ d)`  (compact, the
  finite union of *all* boundary circles; `frontier (raw P) ⊆ bcircles P`)
- `V := fill (raw P)` — the hole-filled open piece (Step L4). Note `frontier V ⊆
  frontier (raw P) ⊆ bcircles P` (L4 shows filling only shrinks the frontier).

`closedPiece P := closure V` will be the compact set the retraction targets.

### 1.2 Genericity predicate `Generic P`

A conjunction of conditions, each realised by countable exclusion (§1.3). Let the
**active circles** be `circ d` for `d ∈ P.pos ∪ P.neg`.

- **G1 (transversality).** For every pair of active circles whose charts overlap,
  in the common conformal coordinate the two circles are disjoint or cross
  transversally (nonzero angle). Equivalently: at each intersection point the two
  circles are not tangent.
- **G2 (no triple points).** No point of `X` lies on three active circles.
- **G3 (compact seating).** For each disk, `closedBall c ρ ⊆ e.target` with room:
  the circle stays away from `frontier e.target`, so `circ d` is compact in
  `e.source` and its exterior-tangent disks fit in `e.target`.
- **G4 (convex frontier corners — the payoff of D1/D2).** Every point of
  `frontier V` lying on two active circles is a **convex corner of `V`**: `V`
  occupies exactly *one* of the 4 local sectors (equivalently, the local
  complement of `V` contains a closed half-disk). This is *arranged*, not merely
  avoided: after choosing `pos`, every exposed positive-positive crossing is
  rounded by a `neg` disk placed in the reflex notch; genericity of the `neg`
  radii then makes each new (pos,neg) and (neg,neg) crossing convex (§1.4).

`Generic P` also records the combinatorial data used downstream: the finite set
`corners P` of crossing points and, for each active circle, the finite set of
crossing points cutting it into finitely many open **arcs**, each entirely inside
`V`, entirely on `frontier V`, or entirely in the complement (arc-insideness is
locally constant off `corners P`).

### 1.3 Countable-exclusion lemmas (how genericity is obtained)

The engine is real-analyticity + conformality of transitions. State these as
standalone lemmas (file `Piece/Generic.lean`):

- **`finite_tangency_radii`** *(S/M).* Fix a chart `e`, center `c`, and a compact
  analytic arc `A ⊆ e.target` (image of another circle under a holomorphic
  transition, or that circle itself). The set `{ρ > 0 | sphere c ρ is tangent to
  A}` is finite. *Proof idea:* tangency at `x∈A` means `ρ = ‖x−c‖` and the radial
  direction is normal to `A`; the function `g : A → ℝ`, `g(x)=‖x−c‖`, is
  real-analytic on the compact 1-manifold `A`, tangency radii are exactly its
  **critical values**; a non-constant real-analytic function on a compact interval
  has finitely many critical points, hence finitely many critical values. (`A`
  cannot be a `c`-centered circle by G3 seating, so `g` is non-constant.)
  *Mathlib:* `AnalyticOn`, `Complex`/`RealAnalytic` isolated-zeros
  (`AnalyticOnNhd.eqOn_zero_of...`), compactness of `A`. Fallback if a clean "real
  analytic ⇒ finite critical values" lemma is missing: prove the weaker
  **countability** of the bad set by isolated-zeros of the derivative and a
  `Set.Countable` union — countability suffices everywhere below.
- **`finite_triplePoint_radii`** *(S).* Given two active circles with their
  finite crossing set `S`, the set of radii `ρ` making a third circle
  `sphere c ρ` pass through a point of `S` is finite (`ρ ∈ {‖s−c‖ : s∈S}`).
- **`exists_generic_radius`** *(M).* Given a center `c`, an open interval
  `(a,b)` of admissible radii with `closedBall c b ⊆ e.target`, and finitely many
  active circles/arcs already fixed, there is `ρ ∈ (a,b)` avoiding all tangency
  radii (G1) and all triple-point radii (G2) — a finite/countable bad set inside
  an uncountable interval. Because `(a,b)` may be taken with `b` as large as
  `e.target` allows, we retain freedom to make disks **large enough to cover** `K`.
- **`exists_generic_pieceData`** *(M).* Iterating `exists_generic_radius` over the
  finitely many chosen disks (positives first, then rounding negatives, §1.4)
  yields `P` with `Generic P`. Order matters: fix each disk's radius avoiding the
  finite bad set generated by all previously fixed circles.

### 1.4 Choosing `pos`, then rounding with `neg`

- **Cover + connect `K`.** `K` compact ⇒ finitely many chart-centered open disks
  `odisk dₖ` cover `K`; enlarge/add disks so that the **nerve is connected** and
  `x₀`'s disk is included (path-connect `x₀` to each cover disk in `X`, cover the
  connecting path by finitely many disks — `IsCompact.elim_finite_subcover`). This
  gives `pos` with `⋃ odisk (pos) ⊇ K` and connected union (Step L1).
- **Round exposed corners.** Compute `corners₀ = pairwise crossings of positive
  circles`. For each `p ∈ corners₀` that (after provisional hole-filling) still
  lies on the frontier, place a `neg` disk `d_p` in `p`'s reflex notch: a small
  disk, in the chart of one incident positive circle, whose *open* carrier is
  contained in the local complement sector and whose *boundary* passes just
  outside `p`, converting the reflex corner into a short concave `neg`-circle arc
  with two convex `(pos,neg)` corners. Radii of `neg` disks are chosen generic
  (G1/G2 with respect to *all* circles) and small enough to be pairwise "local"
  (each `neg` disk meets only the two positive circles of its corner) — a finite
  smallness constraint. This is the geometric heart; rate **L** (Step L3 proves it
  delivers G4 and the exterior-disk property).

---

## 2. Lemma decomposition (Steps L1–L10)

Each step is sized for one focused agent in one file. "In/out" are informal but
precise; difficulty S/M/L/XL.

### L1 — Cover, connect, seat the disks  *(M)*
**In:** `hK`, `hx₀`, path-connectedness, local compactness.
**Out:** `∃ pos : Finset ChartDisk`, `x₀`'s disk ∈ `pos`, `K ⊆ ⋃ d∈pos, odisk d`,
the union `⋃ odisk` is connected, and `closure (⋃ odisk)` compact.
**Tools:** `IsCompact.elim_finite_subcover`, `PathConnectedSpace`, chart
existence (`chartAt`, `chartAt_mem_riemannAtlas`), `IsCompact.finite_...`.
**Risks:** connectivity of the nerve — handle by covering each connecting path,
not by cleverness. Compact closure: finite union of compact `disk`s.

### L2 — Realise genericity  *(M, depends L1 + §1.3)*
**In:** the `pos` from L1.
**Out:** `P : PieceData` with `P.pos = pos` (radii nudged), `P.neg` the rounding
disks, and `Generic P`; still `K ⊆ ⋃ odisk (P.pos)` and connected.
**Tools:** `exists_generic_pieceData`, `finite_tangency_radii`,
`finite_triplePoint_radii`. **Risks:** the "real-analytic ⇒ finite critical
values" lemma; fallback to countability (§1.3). Nudging radii must preserve the
cover of `K` (choose nudge < margin between `K` and the circles).

### L3 — Exterior disk at every frontier point  *(L)*
**In:** `Generic P`, `V := fill (raw P)`.
**Out:** `∀ ξ ∈ frontier V, ExteriorDiskAt V ξ`.
**Structure:** `frontier V ⊆ bcircles P`. Case on `ξ`:
- **Smooth arc point** (`ξ` on one active circle `circ d`, not a corner):
  exterior disk = a small round disk in `d`'s chart **externally tangent** to
  `circ d` at `e ξ` on the side away from `V`. For a *positive* circle `V` is
  locally the disk interior, exterior disk sits outside `disk d` (externally
  tangent, interior disjoint from `disk d` ⊇ local `V`). For a *negative* circle
  `V` is locally outside `disk d`, exterior disk = a sub-disk of `disk d`
  internally tangent at `e ξ` (interior ⊆ `disk d` ⊆ complement of `V`). Both
  give `dist (e ξ) c = r` and `ball ⊆ e.target` by G3.
- **Convex corner** (`ξ` on two circles, G4 ⇒ `V` = one sector): the local
  complement contains a closed half-disk; take the exterior disk as a round disk
  in that half-disk tangent at `e ξ`. Convexity (angle `< π` for `V`, `> π` for
  complement) is exactly what makes a half-plane-sized ball fit.
**Tools:** conformality (angles), `Metric.closedBall/ball/sphere`,
`dist`, G3, G4. Elementary planar geometry, but many cases; the corner case is
the crux and depends on L3's own "G4 ⇒ half-disk in complement" sublemma.
**Risks:** getting the tangency/containment inequalities right in the chart;
ensuring `∀ x ∈ V ∩ e.source, e x ∉ ball c r` uses G2 (only two circles matter
near `ξ`, so the local picture is exactly two conformal lines).

### L4 — Hole-filling: definition and point-set properties  *(L)*
**In:** any open `U` with compact closure in `X` (apply to `U = raw P`).
**Def:** `fill U := U ∪ (⋃ of bounded — i.e. relatively compact — connected
components of Uᶜ)`. Formally, `fill U := U ∪ {x | the component of x in Uᶜ has
compact closure}` (equivalently: not contained in the unique unbounded end).
**Out (all needed downstream):**
- `IsOpen (fill U)`  *(uses local connectedness: components of the open set `Uᶜ`
  interior are open; but `Uᶜ` is closed — use components of the open set
  `(closure U)ᶜ` plus a collar; see below).* 
- `U ⊆ fill U`, `closure (fill U)` compact.
- `frontier (fill U) ⊆ frontier U` — **filling only shrinks the frontier**, so L3
  regularity (proved for `frontier (raw P) ⊆ bcircles`) transfers verbatim to
  `frontier V`. Prove: a frontier point of `fill U` cannot be an added
  (relatively compact component interior) point (those are interior), so it lies
  in `frontier U`.
- Complement structure: `(fill U)ᶜ` has **no relatively compact component**
  (they were all absorbed); every component of `(fill U)ᶜ` is unbounded (its
  closure noncompact). This is what L5–L8 consume.
- If `U` connected then `fill U` connected.
**Tools:** `connectedComponentIn`, `IsPreconnected`, `LocallyConnectedSpace`,
`IsCompact`, `frontier` lemmas (`frontier_subset_closed`, `isOpen.frontier_eq`).
**Risks:** the correct formal notion of "relatively compact component" for a
*closed* complement in a locally compact non-metrizable-but-manifold space.
Recommended precise definition: components of the **open** set `Uᶜ`? `Uᶜ` is
closed, not open. Use instead: `x` is *fillable* iff `x ∉ U` and the connected
component of `x` in `Uᶜ` is compact. Openness of `fill U` then needs: the union
of compact components is open — true because the noncompact end is closed (in a
locally compact, locally connected, connected, noncompact `X`, the union of
non-compact-closure components of a closed set with compact frontier is closed;
prove via `X` noncompact ⇒ a unique end). This is fiddly; give it full L weight.

### L5 — Complement ends are collared 1-manifolds (arc-cycle structure)  *(XL)*
**In:** `Generic P`, `V`, `Z` = closure of a connected component of `Vᶜ`
(equivalently of `(fill (raw P))ᶜ`; `Z` noncompact by L4).
**Out:** a **bicollar of `frontier Z`**: `frontier Z` is a compact topological
1-submanifold of `X` equal to a finite union of active-circle arcs meeting in
pairs at convex corners; there is an open `N ⊇ frontier Z` and a homeomorphism
`N ≃ (frontier Z) × (−1,1)` with `frontier Z ↔ {s=0}`, `N ∩ V ↔ {s>0}`,
`N ∩ interior Z ↔ {s<0}`. Package minimally as: `∃ N s`, `s : N → (−1,1)`
continuous, `frontier Z = s ⁻¹' {0}`, `N ∩ V = s ⁻¹' Ioo 0 1`, plus for each
connected **component** `γ` of `frontier Z` a product chart `γ × (−1,1) ≃ N_γ`.
**Method:** the two-arcs-through-a-corner local model is the circular analogue of
`Moise/PolygonalJordan.lean`'s `puncturedBall_subset_twoSectors_union_rays` and
`openAngularSector`; the along-an-arc collar is the analogue of `edgeTube` /
`edgePositiveSide`/`edgeNegativeSide`. Trace the boundary combinatorially
(cyclic successor at each corner picks the other exposed arc) to assemble each
`γ` and its collar.
**Tools:** template `edgeCoordinate`, `edgeTube`, `openAngularSector`,
`isPathConnected_*`, `Metric.thickening` separation lemmas; conformality to move
the round-circle normal (radial) coordinate into `X`.
**Risks:** this is the largest step. Fallbacks in §3.

### L6 — Crossing parity ⇒ each complement end has connected frontier  *(XL)*
**In:** the bicollar of L5 for a component `γ` of `frontier Z`; `SimplyConnectedSpace X`.
**Out:** `frontier Z` is connected (a single `γ`).
**τ construction (exactly):** For a hypothesised component `γ` of `frontier Z`
with bicollar `N_γ ≃ γ × (−1,1)` and normal coordinate `s`, choose smooth
`λ : (−1,1) → ℝ` with `λ = 0` near `−1`, `λ = 1` near `+1`, monotone. Define

```
τ : X → Circle,   τ x = Circle.exp (2π · λ (s x))   for x ∈ N_γ,   τ x = 1 else.
```

Continuity + `τ ≡ 1` off `N_γ`: at `|s|→1`, `λ ∈ {0,1}` so `Circle.exp(2πλ)=1`,
matching the constant `1` outside; on the `γ`-direction `N_γ` is a product so `τ`
is well-defined. `τ` is continuous (glue on the closed cover `closure N_γ`, `X ∖
N_γ`).
**Winding contradiction (the Moise/NoRetraction pattern):** Assume `frontier Z`
has a second component `γ' ≠ γ`. Pick `p ∈ γ`, `p' ∈ γ'`; connect them by
`δ₁ ⊆ interior Z` and `δ₂ ⊆ V ∪ frontier` (`Kₙ`-side), each transversal to
`γ,γ'`, meeting `γ` only at `p` — existence via path-connectedness of `Z` and of
`V` and a general-position wiggle in charts (the "connect two points by a simple
transversal path" input; A–S: "both open and closed"). The loop `δ = δ₁ ∗ δ₂`
crosses `γ` exactly once transversally (from `s<0` to `s>0`) and never elsewhere
enters `N_γ`. Then:
- `τ ∘ δ : I → Circle` has an **explicit lift** `Λ(t) = 2π · λ(s(δ t))` on the
  crossing sub-interval and `= const` elsewhere, with
  `Λ(1) − Λ(0) = 2π·(1−0) = 2π ≠ 0`.
- `SimplyConnectedSpace X` ⇒ `δ` is homotopic rel `{0,1}` to the constant loop
  (`SimplyConnectedSpace.paths_homotopic`). By
  `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` for `Circle.isCoveringMap_exp`
  (with `ContinuousMap.HomotopicRel.comp_continuousMap` to push the homotopy
  through `τ`), the lift of `τ ∘ δ` and the lift of `τ ∘ const` share endpoints,
  forcing `Λ(1) = Λ(0)`. Contradiction with `2π ≠ 0` (`Real.pi_ne_zero`).
**Tools:** `Circle.isCoveringMap_exp`, `IsCoveringMap.liftPath`,
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`,
`ContinuousMap.HomotopicRel.comp_continuousMap`, `SimplyConnectedSpace.paths_homotopic`,
`Circle.exp_add`. Copy the endpoint-of-lift bookkeeping from
`no_retraction_closedUnitDisk`.
**Risks:** building `δ` transversal and crossing exactly once (general position);
the explicit lift `Λ` and "crosses once" bookkeeping. §3 fallback.

### L7 — Escaping ray in an unbounded end  *(M/L)*
**In:** `Z` noncompact connected, locally compact, locally path-connected.
**Out:** a proper continuous injective `δ : [0,∞) → interior Z` (or `[0,1) → Z`)
escaping every compact set (`∀ C compact, ∃ t₀, ∀ t>t₀, δ t ∉ C`), starting at a
chosen `p ∈ γ = frontier Z`.
**Method:** exhaust `Z` by compacts (`Z` σ-compact via manifold + second-countable
*if available*; otherwise build the ray by chaining charts: pick `xₙ` leaving each
`Kₙ`, connect `xₙ` to `xₙ₊₁` by a path in `Z`, concatenate; injectivity by a
general-position wiggle or drop injectivity if L8 only needs a proper *map*).
**Tools:** `exists_compact_superset`, `LocallyCompactSpace`, path-connectedness of
`Z`. **Risks:** `X` second-countability is **not** in the frozen hypotheses; do
not assume σ-compactness. Build the escaping ray from local compactness +
connectedness directly. Injectivity is the only hard part — see §3 (L8 can be
rephrased to avoid needing an *embedded* ray).

### L8 — Tietze / FrontierGlue retraction ⇒ `SimplyConnectedSpace (closure V)`  *(L)*
**In:** for every unbounded component `Z` of `Vᶜ`: `frontier Z` connected (L6),
parametrised `γ_Z : I → frontier Z` with `γ_Z 0 = γ_Z 1 = p_Z` (a loop onto the
1-manifold circle from L5); an escaping ray `δ_Z` (L7).
**Out:** a retraction `r : X → closure V` with `r|closure V = id`, hence
`SimplyConnectedSpace (closure V)`.
**Method (A–S §6, using `Moise/FrontierGlue.lean`):** cut `Z` along `δ_Z` to
`Z̃` with connected boundary `δ' ∪ [p',p''] ∪ δ''`; define `μ : ∂Z̃ → [0,1]`
(`0` on `δ'`, `γ_Z⁻¹` on the `γ`-part, `1` on `δ''`); Tietze-extend to
`μ̃ : Z̃ → [0,1]` (`ContinuousMap.exists_restrict_eq` / `exists_extension`, target
`I` or `ℝ` then clamp); descend `γ_Z ∘ μ̃` to `Ψ_Z : Z → frontier Z ⊆ closure V`;
glue with `id` on `closure V` via `frontierGlue`/`continuous_frontierGlue_of_matches`
(the `MatchesAtFrontier` obligation is immediate since `Ψ_Z = id` on `frontier Z`).
Retract argument: `i : closure V ↪ X`, `r ∘ i = id`, `X` simply connected ⇒
`closure V` simply connected. Concretely: `IsPathConnected (closure V)`
(from L4 connectivity + closure) and every loop `p` in `closure V` satisfies
`p ≃ (r ∘ i ∘ p) = r∘(i∘p)`; `i∘p` null-homotopic in `X`; push through `r`
(`ContinuousMap.Homotopy.compContinuousMap`) ⇒ null-homotopic in `closure V`.
**Tools:** `Moise/FrontierGlue.lean` (`frontierGlue`, `continuous_frontierGlue_of_matches`,
`MatchesAtFrontier`), `ContinuousMap.exists_restrict_eq` (Tietze),
`ContinuousMap.Homotopy.compContinuousMap`, `simply_connected_iff_paths_homotopic'`.
**Risks:** the "cut along `δ` to a surface with connected boundary" is topological
surgery; formalise as a *pushout/quotient* only as far as needed — actually only
`Ψ_Z : Z → frontier Z` continuous with `Ψ_Z|frontier Z = id` is needed; build it
directly (Tietze on `Z` with boundary data) and skip explicit `Z̃` if possible.

### L9 — Inner-collar transfer: `SimplyConnectedSpace (closure V) ⇒ IsSimplyConnected V`  *(XL)*
**In:** `SimplyConnectedSpace (closure V)`; the *inner* half `s>0` of the L5
bicollars (a collar of `frontier V` from **inside** `V`); `IsConnected V`.
**Out:** `IsSimplyConnected V` (i.e. `SimplyConnectedSpace ↥V`).
**Method:** build an **inward push** homotopy `F : I × closure V → closure V`,
`F 0 = id`, `F 1 '' closure V ⊆ V`, `F s '' V ⊆ V` for all `s`, using the inner
collars to slide `frontier V` to `s = +ε` while fixing an interior core. Then
`incl : V ↪ closure V` and `F 1 : closure V → V` are homotopy inverses ⇒ `π₁`
iso ⇒ `IsSimplyConnected V` (path-connectedness of `V` from `IsConnected V` +
local path-connectedness). Use `isSimplyConnected_iff_exists_homotopy_refl_forall_mem`
as the target characterisation: every loop in `V` extends to a homotopy to a
constant staying in `V` — obtain it by pushing a `closure V`-null-homotopy
inward with `F`.
**Tools:** L5 collars, partition of unity to glue per-arc radial pushes
(`SmoothPartitionOfUnity`/`continuous` bump), `ContinuousMap.Homotopy`,
`isSimplyConnected_iff_exists_homotopy_refl_forall_mem`.
**Risks:** the hardest transfer; global inward push glued across corners. §3.

### L10 — Final assembly  *(S/M)*
**In:** L1–L9 outputs for `V := fill (raw P)`.
**Out:** the full existential. Conjuncts:
- `IsOpen V` (L4), `IsConnected V` (L1+L4), `IsCompact (closure V)` (L1+L4),
  `K ⊆ V` (`K ⊆ ⋃ odisk ⊆ raw P`? — ensure `neg` disks miss `K`: choose rounding
  disks disjoint from `K` since `K` is interior to the positive union; add to
  `Generic`), `IsSimplyConnected V` (L9),
- `(frontier V).Nonempty`: `closure V` compact + `X` noncompact ⇒ `V ≠ X`; `V`
  nonempty; in a connected space a nonempty proper subset has nonempty frontier
  (`frontier_nonempty_of_...`; or: `V` clopen would contradict `ConnectedSpace`).
- `∀ ξ ∈ frontier V, ExteriorDiskAt V ξ` (L3 + L4 frontier-shrink).
**Risks:** ensuring `K ⊆ V` survives the `neg` subtraction (rounding disks placed
away from `K`) and hole-filling (filling only grows `V`).

---

## 3. The three fragile steps and their fallbacks

### Risk A — L5 (collared 1-manifold structure of complement frontiers)
This is the most infrastructure-heavy step (a from-scratch "boundary of a
piecewise-circular region is a bicollared 1-manifold").
- **Fallback A1 (single-chart cells).** Strengthen the construction so each
  complement-end frontier component lies in **one chart** (arrange positive disks
  so that boundary arc-cycles never leave a single chart — feasible when `K` is
  covered by a locally-finite chart family and pieces are built chart-by-chart on
  a tree, §4). Then L5 is *exactly* the planar `Moise/PolygonalJordan.lean`
  strip/collar toolkit transported by one conformal chart — reuse `edgeTube`,
  `openAngularSector`, `StripScales` almost verbatim.
- **Fallback A2 (weaken the output).** L6's τ only needs, per component `γ`, a
  single continuous normal coordinate `s` on an open `N ⊇ γ` with the two-sided
  sign property and `γ = s⁻¹{0}`. This is *weaker* than a full product bicollar;
  build `s` as a signed distance-to-`γ` in charts (glued by a partition of unity)
  without proving `N ≅ γ×(−1,1)`. Halves the L5 burden.
- **Fallback A3 (bypass arc-cycles for L8).** L8's retraction needs `frontier Z`
  connected and a loop parametrisation `γ_Z`; if L5 only yields "compact,
  connected, locally an arc," a Hahn–Mazurkiewicz surjection `I ↠ frontier Z`
  plus Tietze may suffice without an explicit 1-manifold atlas.

### Risk B — L6 (crossing-parity τ and the once-crossing loop)
- **Fallback B1.** Build `δ` and the "crosses `γ` exactly once" fact using the
  bicollar coordinate `s`: `δ` transversal ⇔ `s∘δ` changes sign once. Reduce
  "connect two points by a transversal simple path" to: connect by *any* path
  (path-connectedness), then perturb in charts to be transversal to the finitely
  many active circles (general position, countable exclusion again). Simplicity of
  `δ` is **not needed** for the winding argument — only the crossing count of `γ`
  matters — so drop injectivity of `δ`.
- **Fallback B2.** If assembling one global `τ` per component is hard, use the
  **relative** form: it suffices that `τ ∘ δ` is a non-null loop in `Circle`;
  work with `τ` defined only on `N_γ ∪ (X ∖ γ')`-neighbourhoods as needed. The
  covering-lift contradiction (`no_retraction_closedUnitDisk` skeleton) is robust.

### Risk C — L9 (open/closed simple-connectivity transfer)
This is a genuine, unavoidable cost (D4/§4 justify why no route dodges it).
- **Fallback C1 (explicit per-disk push).** Since `V` is disks-minus-disks, build
  the inward push chart-locally: inside each positive disk, radial scaling toward
  its center; inside each subtracted `neg` region, radial scaling away; glue by a
  partition of unity subordinate to the chart cover. Concreteness beats generality.
- **Fallback C2 (deformation retraction of `closure V` onto an interior core).**
  Prove `closure V` strong-deformation-retracts onto a compact `V₀ ⊆ V` with
  `V₀ ≃ closure V`; then `π₁ V₀ = π₁ closure V = 0` and `V₀ ↪ V ↪ closure V`
  with the outer inclusion a homotopy equivalence forces `π₁ V = 0`.
- **Fallback C3 (escalate to orchestrator).** If L9 proves intractable, the
  cheapest *statement-preserving* mitigation is to **build `V` with a manifestly
  collared boundary** (a genuine smooth 1-manifold frontier via hand-built smooth
  attaching collars instead of transversal circle crossings), making
  `V ≃ closure V` structural. This trades L5/L6 complexity for L9 simplicity; the
  orchestrator should weigh this globally.

---

## 4. Can a stronger construction simplify things?

- **Tree-of-disks with single-chart cells (recommended add-on).** Build the piece
  by a spanning **tree** over a locally-finite chart cover: root at `x₀`'s chart,
  attach each child disk overlapping its parent inside the *overlap chart*. Then
  (i) every boundary arc-cycle stays inside a single chart neighbourhood
  (unblocks Fallback A1, collapsing L5 onto the planar Moise toolkit), and (ii)
  corner rounding (D1) is likewise single-chart. This meaningfully de-risks the
  two XL topological steps at the cost of a more disciplined L1/L2. **Adopt it.**
- **Direct loop argument vs. A–S retraction (D4 decision, justified).** The
  "every loop in `V` is null-homotopic in `V`" route composes an `X`-null-homotopy
  with a retraction `r`. But any retraction that is `id` on `V` and continuous
  must send `frontier V` to `frontier V ⊄ V` (continuity forces it), so its image
  lands in `closure V`, not `V`; the resulting null-homotopy lives in `closure V`
  and must still be pushed into `V` — i.e. it re-incurs L9. Hence the direct route
  saves nothing and loses the clean `SimplyConnectedSpace (closure V)` milestone.
  **Choose the A–S retraction to `closure V` (L8) + inner-collar transfer (L9).**
- **Convex-corner rounding vs. smooth collars.** D1's disk-subtraction keeps
  everything algebraic (disks and spheres, reusing Metric API) but makes L5/L9
  handle corners. The alternative — hand-built smooth attaching collars (no
  corners at all) — simplifies L9 to near-triviality (structural
  `V ≃ closure V`) but pushes work into constructing/΅reasoning about smooth
  bump-collars and re-verifying `ExteriorDiskAt` on curved smooth boundary. Net:
  keep D1 (disks) unless L9 stalls, then invoke Fallback C3.

---

## 5. File layout, dependency DAG, parallelism

Proposed modules under `Uniformization/Surface/` (namespace `Uniformization`,
`open Rado`):

```
Piece/Data.lean        -- PieceData, ChartDisk, disk/odisk/circ, basic topology   (L0 scaffolding)
Piece/Generic.lean     -- Generic predicate, countable-exclusion lemmas (§1.3)     (L2 deps)
Piece/Cover.lean       -- L1 cover+connect+seat; tree-of-disks builder (§4)
Piece/Round.lean       -- L3 exterior-disk-at-frontier + corner rounding (§1.4, G4)
Fill/HoleFill.lean     -- L4 fill def + point-set properties
Fill/Collar.lean       -- L5 bicollar / arc-cycle structure of complement frontiers
Fill/CrossingParity.lean -- L6 τ:X→Circle + winding ⇒ frontier connected
Fill/EscapingRay.lean  -- L7 proper ray in an unbounded end
Fill/Retraction.lean   -- L8 Tietze/FrontierGlue retraction ⇒ s.c. of closure V
Fill/CollarTransfer.lean -- L9 inner-collar ⇒ IsSimplyConnected V
Surface/Fill.lean      -- L10 assembles exists_simply_connected_piece (existing file)
```

Port `Moise/PolygonalJordan.lean` (collar/sector toolkit), `Moise/FrontierGlue.lean`,
`Moise/NoRetraction.lean` skeleton into `reference`-mirrored helpers or import
patterns as the single-chart local models for L5/L6/L8.

**Dependency DAG:**

```
Data ─┬─> Generic ─┬─> Cover ──┐
      │            │           ├─> Round(L3) ──┐
      └────────────┘           │               │
Cover ───────────────────────> Round           │
Round ─> HoleFill(L4) ─┬─> Collar(L5) ─┬─> CrossingParity(L6) ─┐
                       │               │                       │
                       ├─> EscapingRay(L7) ────────────────────┤
                       └─> CollarTransfer(L9, needs L5 inner) ──┤
Collar(L5)+CrossingParity(L6)+EscapingRay(L7) ─> Retraction(L8) ┤
Retraction(L8) ────────────────────────────────> CollarTransfer(L9)
HoleFill+Round+L9 ─────────────────────────────> Fill.lean(L10)
```

**Parallelisable clusters (independent agents):**
- Cluster α: `Data`, then `Generic` + `Cover` in parallel.
- Cluster β (after `HoleFill`): `Collar (L5)`, `EscapingRay (L7)`, and `Round (L3)`
  are mutually independent — run in parallel.
- `CrossingParity (L6)` waits on `Collar`; `Retraction (L8)` waits on L5+L6+L7;
  `CollarTransfer (L9)` waits on L5+L8; `Fill (L10)` last.
- The three Moise-template ports can be done up front, fully in parallel with
  Cluster α.

---

## 6. Ten-line summary for the orchestrator

1. Geometry decision: pieces are **closed chart disks minus small corner-rounding
   disks**, hole-filled — *not* plain disk unions.
2. **Critical finding (D2):** a union-of-disks piece **fails `ExteriorDiskAt`** at
   every transversal boundary crossing (V fills 3 of 4 conformal sectors ⇒ no
   exterior ball fits); corner-rounding via subtracted disks is the fix.
3. Genericity = transversal crossings, no triple points, convex frontier corners;
   obtained by **countable exclusion** of tangency/triple-point radii (real-analytic
   critical values are finite; countability suffices as fallback).
4. Ten lemma steps L1–L10; the two XL topological steps are L5 (bicollar/arc-cycle
   structure) and L9 (open→closed simple-connectivity transfer); L6 (crossing-parity
   `τ:X→Circle`) is XL but has a clean `NoRetraction`/`Circle.isCoveringMap_exp` template.
5. Simple connectivity route: **A–S retraction to `closure V`** (⇒
   `SimplyConnectedSpace (closure V)`) then **inner-collar transfer** to open `V`;
   the "direct loop" alternative provably re-incurs the same collar, so rejected.
6. Strong recommendation: build pieces as a **tree of single-chart-cell disks**, so
   L5/L6 reduce to the planar `Moise/PolygonalJordan.lean` toolkit under one conformal
   chart — this de-risks the two hardest steps.
7. Key pin tools confirmed present: `Circle.isCoveringMap_exp`,
   `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`,
   `SimplyConnectedSpace.paths_homotopic`, Tietze (`ContinuousMap.exists_restrict_eq`),
   `isSimplyConnected_iff_exists_homotopy_refl_forall_mem`, manifold ⇒ locally
   compact/connected/path-connected.
8. Non-hypothesis watch: the frozen statement has **no `SecondCountableTopology`**;
   L4/L7 must not assume σ-compactness — build ends/rays from local compactness only.
9. **Statement change:** none required — the frozen theorem is provable as stated
   and is exactly what downstream Green's-function/covering steps need (open `V`,
   simply connected, exterior-disk-regular). Do **not** weaken `IsSimplyConnected V`
   to the closed piece.
10. Optional de-risking lever (orchestrator's call): if L9 stalls, switch the
    geometry to hand-built **smooth attaching collars** (no corners), making
    `V ≃ closure V` structural and L9 near-trivial, at the cost of more work in
    L3/L5 on curved smooth boundary (Fallback C3).
