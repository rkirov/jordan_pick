# Rado library — API map for Green's functions / biholomorphisms on Riemann surfaces

(Surveyed 2026-07-16 from the Rado/ sources at commit 96ccb1d. Signatures copied verbatim.)

## Global conventions (all `Rado.Surface.*` files)

Every surface file opens `Set Topology Metric MeasureTheory InnerProductSpace Complex Filter`, sets `autoImplicit false`, and uses the standard variable block:

```lean
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
```

- The model is written `modelWithCornersSelf ℂ ℂ` (no local notation `mℂ`; the docstrings say `mℂ` but the code always spells it out). Regularity is `1` (C¹ = holomorphic).
- `[T2Space X]` is added only where genuinely needed (harmonic replacement, configuration, étale Hausdorffness, assembly).
- `[ConnectedSpace X]` appears only in `Barriers.isConnected_configY` and the `Assembly` section.
- There is **no** local notation for charts; the code writes `chartAt ℂ x`, `(chartAt ℂ x).symm`, `e.source`, `e.target`, `e.symm`. Charts are `OpenPartialHomeomorph X ℂ`.
- `riemannAtlas X` (see Charts) is the ambient maximal atlas; chart representatives are `F ∘ e.symm` over `chartImage e s`.
- Many theorems are prefixed `omit [IsManifold …]` / `omit [ChartedSpace ℂ X]` — noting exactly which typeclasses each lemma actually needs.

## `Rado/Complex/SubMean.lean`

ℂ-chart-level sub/harmonicity via circle averages (`Real.circleAverage`).

```lean
structure SubMeanOn (g : ℂ → ℝ) (s : Set ℂ) : Prop where
  continuousOn : ContinuousOn g s
  submean : ∀ c r, 0 < r → closedBall c r ⊆ s → g c ≤ circleAverage g c r

structure MeanEqOn (h : ℂ → ℝ) (s : Set ℂ) : Prop where
  continuousOn : ContinuousOn h s
  mean_eq : ∀ c r, 0 < r → closedBall c r ⊆ s → circleAverage h c r = h c
```

```lean
theorem MeanEqOn.subMeanOn {h : ℂ → ℝ} {s : Set ℂ} (hh : MeanEqOn h s) : SubMeanOn h s
theorem MeanEqOn.neg {h : ℂ → ℝ} {s : Set ℂ} (hh : MeanEqOn h s) : MeanEqOn (-h) s
theorem SubMeanOn.mono {g : ℂ → ℝ} {s t : Set ℂ} (hg : SubMeanOn g s) (hts : t ⊆ s) : SubMeanOn g t
theorem SubMeanOn.max {g₁ g₂ : ℂ → ℝ} {s : Set ℂ} (h₁ : SubMeanOn g₁ s) (h₂ : SubMeanOn g₂ s) :
    SubMeanOn (fun z ↦ Max.max (g₁ z) (g₂ z)) s
theorem SubMeanOn.add_meanEq {g h : ℂ → ℝ} {s : Set ℂ} (hg : SubMeanOn g s) (hh : MeanEqOn h s) :
    SubMeanOn (g + h) s
theorem SubMeanOn.const {a : ℝ} {s : Set ℂ} : SubMeanOn (fun _ ↦ a) s
```

Maximum principles:

```lean
theorem SubMeanOn.eqOn_const_of_isMaxOn {g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hsc : IsPreconnected s) (hg : SubMeanOn g s) {x₀ : ℂ} (hx₀ : x₀ ∈ s)
    (hmax : IsMaxOn g s x₀) : EqOn g (fun _ ↦ g x₀) s

theorem SubMeanOn.le_of_frontier_le {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hg : SubMeanOn g U) (hgc : ContinuousOn g (closure U))
    {M : ℝ} (hbd : ∀ x ∈ frontier U, g x ≤ M) : ∀ x ∈ closure U, g x ≤ M

theorem MeanEqOn.eqOn_closure_of_frontier {u v : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hu : MeanEqOn u U) (hv : MeanEqOn v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hb : EqOn u v (frontier U)) : EqOn u v (closure U)
```

## `Rado/Complex/Poisson.lean`

Dirichlet existence via the Schwarz integral. Mathlib anchors: `herglotzRieszKernel`, `poissonKernel`, `poissonKernel_eq_re_herglotzRieszKernel`, `re_herglotzRieszKernel_le`, `DiffContOnCl.circleAverage_poissonKernel_smul`.

```lean
noncomputable def schwarzIntegral (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  Real.circleAverage (fun z ↦ herglotzRieszKernel c w z * (f z : ℂ)) c R
```

Kernel API (convention: in `poissonKernel c w z`, `w` interior, `z` on circle):

```lean
theorem poissonKernel_pos (hw : w ∈ ball c R) (hz : z ∈ sphere c R) : 0 < poissonKernel c w z
theorem circleAverage_poissonKernel (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w) c R = 1
theorem eventually_poissonKernel_le_of_dist {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere c R) (hR : 0 < R)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝[ball c R] ζ₀, ∀ z ∈ sphere c R, δ ≤ dist z ζ₀ → poissonKernel c w z ≤ ε
```

```lean
theorem schwarzIntegral_differentiableOn (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    DifferentiableOn ℂ (schwarzIntegral f c R) (ball c R)
theorem re_schwarzIntegral {w : ℂ} (hR : 0 < R) (hf : ContinuousOn f (sphere c R))
    (hw : w ∈ ball c R) :
    (schwarzIntegral f c R w).re = Real.circleAverage (fun z ↦ poissonKernel c w z • f z) c R
theorem tendsto_re_schwarzIntegral (hR : 0 < R) (hf : ContinuousOn f (sphere c R))
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere c R) :
    Filter.Tendsto (fun w ↦ (schwarzIntegral f c R w).re) (𝓝[ball c R] ζ₀) (𝓝 (f ζ₀))
```

Main theorem ("harmonic" = Mathlib's `InnerProductSpace.HarmonicOnNhd`):

```lean
theorem exists_harmonic_extension {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere c R)) :
    ∃ u : ℂ → ℝ, ContinuousOn u (closedBall c R) ∧
      HarmonicOnNhd u (ball c R) ∧ EqOn u f (sphere c R)
```

## `Rado/Complex/Dirichlet.lean`

```lean
noncomputable def poissonExtension (f : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℝ :=
  if h : 0 < R ∧ ContinuousOn f (sphere c R) then
    fun z ↦ if z ∈ closedBall c R then (exists_harmonic_extension h.1 h.2).choose z else f z
  else f
```

API (`variable {c : ℂ} {R : ℝ} {f : ℂ → ℝ}`):

```lean
theorem poissonExtension_continuousOn (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    ContinuousOn (poissonExtension f c R) (closedBall c R)
theorem poissonExtension_harmonicOnNhd (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    HarmonicOnNhd (poissonExtension f c R) (ball c R)
theorem poissonExtension_eqOn_sphere (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    EqOn (poissonExtension f c R) f (sphere c R)
theorem poissonExtension_eqOn_compl (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    EqOn (poissonExtension f c R) f (closedBall c R)ᶜ
theorem poissonExtension_mem_Icc (hR : 0 < R) (hf : ContinuousOn f (sphere c R))
    {m M : ℝ} (hfm : ∀ z ∈ sphere c R, f z ∈ Icc m M) :
    ∀ z ∈ closedBall c R, poissonExtension f c R z ∈ Icc m M
```

Harmonic ⟺ mean-value; holomorphic precomposition; subharmonic comparison:

```lean
theorem HarmonicOnNhd.meanEqOn {u : ℂ → ℝ} {s : Set ℂ} (hu : HarmonicOnNhd u s) : MeanEqOn u s
theorem MeanEqOn.harmonicOnNhd {u : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s) (hu : MeanEqOn u s) :
    HarmonicOnNhd u s
theorem HarmonicOnNhd.comp_analytic {u : ℂ → ℝ} {t : Set ℂ} (hu : HarmonicOnNhd u t)
    (ht : IsOpen t) {φ : ℂ → ℂ} {s : Set ℂ} (hφ : AnalyticOnNhd ℂ φ s)
    (hmaps : MapsTo φ s t) : HarmonicOnNhd (u ∘ φ) s
theorem SubMeanOn.le_poissonExtension_on {g : ℂ → ℝ} {s : Set ℂ}
    (hg : SubMeanOn g s) {c : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ s) :
    ∀ x ∈ closedBall c R, g x ≤ poissonExtension g c R x
```

## `Rado/Complex/PlanarConnected.lean`

Planar geometry for the fixed two-disk configuration (most helpers `private`):

```lean
theorem isPathConnected_ball_diff_two_disks :
    IsPathConnected (ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1))
theorem config_disks_disjoint : Disjoint (closedBall (-4 : ℂ) 1) (closedBall (4 : ℂ) 1)
theorem config_annuli_subset : closedBall (-4 : ℂ) 2 ∪ closedBall (4 : ℂ) 2 ⊆ ball (0 : ℂ) 8
theorem config_annuli_disjoint : Disjoint (closedBall (-4 : ℂ) 2) (closedBall (4 : ℂ) 2)
```

## `Rado/Surface/Charts.lean`

```lean
abbrev riemannAtlas (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    Set (OpenPartialHomeomorph X ℂ) :=
  IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X
```

```lean
theorem transition_analyticAt {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) (he' : e' ∈ riemannAtlas X) {x : X}
    (hx : x ∈ e.source ∩ e'.source) : AnalyticAt ℂ (e' ∘ e.symm) (e x)
theorem chartAt_mem_riemannAtlas (x : X) : chartAt ℂ x ∈ riemannAtlas X
theorem affine_trans_mem_riemannAtlas {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) {a b : ℂ} (ha : a ≠ 0) :
    ∃ e' ∈ riemannAtlas X, e'.source = e.source ∧ ∀ x ∈ e.source, e' x = a * e x + b
```

Holomorphic maps `X → ℂ`:

```lean
def HolomorphicOn (F : X → ℂ) (s : Set X) : Prop :=
  ∀ x ∈ s, AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)
```

```lean
theorem HolomorphicOn.continuousOn (hF : HolomorphicOn F s) : ContinuousOn F s
theorem HolomorphicOn.mono (hF : HolomorphicOn F s) {t : Set X} (hts : t ⊆ s) : HolomorphicOn F t
theorem HolomorphicOn.analyticAt_comp_symm (hF : HolomorphicOn F s)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X) {x : X}
    (hx : x ∈ s ∩ e.source) : AnalyticAt ℂ (F ∘ e.symm) (e x)
theorem HolomorphicOn.congr_of_eventuallyEq (hG : HolomorphicOn G s)
    (h : ∀ x ∈ s, F =ᶠ[𝓝 x] G) : HolomorphicOn F s
theorem HolomorphicOn.eqOn_of_eventuallyEq (hF : HolomorphicOn F s) (hG : HolomorphicOn G s)
    (hs : IsOpen s) (hsc : IsPreconnected s) {x : X} (hx : x ∈ s)
    (hFG : F =ᶠ[𝓝 x] G) : EqOn F G s        -- identity theorem
```

Point-set instances:

```lean
theorem locallyCompactSpace : LocallyCompactSpace X
theorem locallyConnectedSpace : LocallyConnectedSpace X
theorem locally_secondCountable (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ SecondCountableTopology U
```

## `Rado/Surface/Harmonic.lean`

```lean
def chartImage (e : OpenPartialHomeomorph X ℂ) (s : Set X) : Set ℂ := e '' (s ∩ e.source)

def SurfaceHarmonicOn (u : X → ℝ) (s : Set X) : Prop :=
  ∀ e ∈ riemannAtlas X, HarmonicOnNhd (u ∘ e.symm) (chartImage e s)

structure SurfaceSubharmonicOn (g : X → ℝ) (s : Set X) : Prop where
  continuousOn : ContinuousOn g s
  subMeanOn : ∀ e ∈ riemannAtlas X, SubMeanOn (g ∘ e.symm) (chartImage e s)
```

chartImage helpers (no manifold/charted instances needed):

```lean
theorem isOpen_chartImage (e) {s : Set X} (hs : IsOpen s) : IsOpen (chartImage e s)
theorem chartImage_subset_target (e) (s : Set X) : chartImage e s ⊆ e.target
theorem mem_chartImage_of_mem {e s x} (hx : x ∈ s) (hxe : x ∈ e.source) : e x ∈ chartImage e s
theorem mapsTo_symm_chartImage {e s} : MapsTo e.symm (chartImage e s) s
theorem continuousOn_comp_chart_symm {g : X → ℝ} (e) {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (g ∘ e.symm) (chartImage e s)
```

```lean
theorem SurfaceHarmonicOn.continuousOn (hu : SurfaceHarmonicOn u s) : ContinuousOn u s
theorem SurfaceHarmonicOn.mono (hu : SurfaceHarmonicOn u s) {t : Set X} (hts : t ⊆ s) :
    SurfaceHarmonicOn u t
theorem SurfaceHarmonicOn.of_chartwise
    (h : ∀ x ∈ s, ∃ e ∈ riemannAtlas X, x ∈ e.source ∧ HarmonicAt (u ∘ e.symm) (e x)) :
    SurfaceHarmonicOn u s
theorem SurfaceHarmonicOn.surfaceSubharmonicOn (hu : SurfaceHarmonicOn u s) :
    SurfaceSubharmonicOn u s
theorem SurfaceHarmonicOn.neg (hu : SurfaceHarmonicOn u s) : SurfaceHarmonicOn (-u) s
```

```lean
theorem SurfaceSubharmonicOn.mono (hg : SurfaceSubharmonicOn g s) {t : Set X} (hts : t ⊆ s) :
    SurfaceSubharmonicOn g t
theorem SurfaceSubharmonicOn.max (h₁ : SurfaceSubharmonicOn g₁ s) (h₂ : SurfaceSubharmonicOn g₂ s) :
    SurfaceSubharmonicOn (fun x ↦ Max.max (g₁ x) (g₂ x)) s
theorem SurfaceSubharmonicOn.of_locally {g : X → ℝ} {s : Set X}
    (h : ∀ x ∈ s, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ s ∧ SurfaceSubharmonicOn g V) :
    SurfaceSubharmonicOn g s
```

Local-to-global bridge (ℂ-level):

```lean
structure SubMeanLocalOn (g : ℂ → ℝ) (s : Set ℂ) : Prop where
  continuousOn : ContinuousOn g s
  submean_small : ∀ z ∈ s, ∀ᶠ r in 𝓝[>] (0 : ℝ), g z ≤ Real.circleAverage g z r

theorem SubMeanLocalOn.mono {g s t} (hg : SubMeanLocalOn g s) (hts : t ⊆ s) : SubMeanLocalOn g t
theorem SubMeanLocalOn.eqOn_const_of_isMaxOn {g s} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hg : SubMeanLocalOn g s) {x₀ : ℂ} (hx₀ : x₀ ∈ s) (hmax : IsMaxOn g s x₀) :
    EqOn g (fun _ ↦ g x₀) s
theorem SubMeanLocalOn.le_of_frontier_le {g U} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hg : SubMeanLocalOn g U) (hgc : ContinuousOn g (closure U)) {M : ℝ}
    (hbd : ∀ x ∈ frontier U, g x ≤ M) : ∀ x ∈ closure U, g x ≤ M
theorem SubMeanLocalOn.subMeanOn {g s} (hg : SubMeanLocalOn g s) : SubMeanOn g s
```

## `Rado/Surface/Perron.lean`

```lean
noncomputable def surfaceReplace (g : X → ℝ) (e : OpenPartialHomeomorph X ℂ)
    (c : ℂ) (r : ℝ) : X → ℝ := fun x ↦
  if _h : x ∈ e.source ∧ e x ∈ closedBall c r then
    poissonExtension (g ∘ e.symm) c r (e x)
  else g x

structure IsReplaceDisk (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ) (s : Set X) : Prop where
  mem_atlas : e ∈ riemannAtlas X
  r_pos : 0 < r
  closedBall_subset : closedBall c r ⊆ e.target
  preimage_subset : e.symm '' closedBall c r ⊆ s
```

```lean
theorem IsReplaceDisk.compact_preimage (hd : IsReplaceDisk e c r s) :
    IsCompact (e.symm '' closedBall c r)
theorem surfaceReplace_eqOn_compl : EqOn (surfaceReplace g e c r) g (e.symm '' closedBall c r)ᶜ
theorem surfaceReplace_surfaceSubharmonicOn [T2Space X] (hs : IsOpen s)
    (hg : SurfaceSubharmonicOn g s) (hd : IsReplaceDisk e c r s) :
    SurfaceSubharmonicOn (surfaceReplace g e c r) s
theorem le_surfaceReplace (hg : SurfaceSubharmonicOn g s) (hd : IsReplaceDisk e c r s) :
    ∀ x ∈ s, g x ≤ surfaceReplace g e c r x
theorem surfaceReplace_surfaceHarmonicOn (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) : SurfaceHarmonicOn (surfaceReplace g e c r) (e.symm '' ball c r)
theorem surfaceReplace_mem_Icc (hg : SurfaceSubharmonicOn g s) (hd : IsReplaceDisk e c r s)
    (hb : ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1) :
    ∀ x ∈ s, surfaceReplace g e c r x ∈ Icc (0 : ℝ) 1
```

```lean
structure IsPerronFamily (𝓕 : Set (X → ℝ)) (s : Set X) : Prop where
  nonempty : 𝓕.Nonempty
  subharmonic : ∀ g ∈ 𝓕, SurfaceSubharmonicOn g s
  bounds : ∀ g ∈ 𝓕, ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1
  max_mem : ∀ g₁ ∈ 𝓕, ∀ g₂ ∈ 𝓕, (fun x ↦ Max.max (g₁ x) (g₂ x)) ∈ 𝓕
  replace_mem : ∀ g ∈ 𝓕, ∀ e c r, IsReplaceDisk e c r s → surfaceReplace g e c r ∈ 𝓕

noncomputable def perronSup (𝓕 : Set (X → ℝ)) : X → ℝ := fun x ↦ sSup ((fun g ↦ g x) '' 𝓕)
```

⚠ NOTE: `IsPerronFamily.bounds` hardwires values into `Icc 0 1` — a Green's-function
family (unbounded, with −log pole) needs either a renormalization into [0,1] or a
generalization of this structure.

```lean
theorem IsPerronFamily.surfaceHarmonicOn_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    (hs : IsOpen s) (h𝓕 : IsPerronFamily 𝓕 s) : SurfaceHarmonicOn (perronSup 𝓕) s
theorem IsPerronFamily.le_perronSup {𝓕 s} (h𝓕 : IsPerronFamily 𝓕 s) {g : X → ℝ} (hg : g ∈ 𝓕) :
    ∀ x ∈ s, g x ≤ perronSup 𝓕 x
theorem IsPerronFamily.perronSup_le {𝓕 s} (h𝓕 : IsPerronFamily 𝓕 s) {M : ℝ} {x : X}
    (hM : ∀ g ∈ 𝓕, g x ≤ M) : perronSup 𝓕 x ≤ M
```

(Harnack is `private harmonicOnNhd_ciSup_of_monotone` / `harnack_le` — not exported;
re-derive or re-export if needed.)

```lean
theorem subMeanOn_congr {g₁ g₂ : ℂ → ℝ} {s : Set ℂ} (hg : SubMeanOn g₁ s) (h : EqOn g₂ g₁ s) :
    SubMeanOn g₂ s
theorem surfaceSubharmonicOn_congr {g₁ g₂ : X → ℝ} {s : Set X}
    (hg : SurfaceSubharmonicOn g₁ s) (h : EqOn g₂ g₁ s) : SurfaceSubharmonicOn g₂ s
```

## `Rado/Surface/Barriers.lean`

Two-disk configuration and log-barriers:

```lean
def configY : Set X := univ \ (e.symm '' closedBall (-4) 1 ∪ e.symm '' closedBall 4 1)

def configFamily : Set (X → ℝ) :=
  {g | SurfaceSubharmonicOn g (configY e) ∧ (∀ x ∈ closure (configY e), g x ∈ Icc (0 : ℝ) 1)
      ∧ ContinuousOn g (closure (configY e))
      ∧ ∀ x ∈ closure (configY e) ∩ e.symm '' closedBall (-4) 1, g x ≤ 0}

theorem closedBall_config_subset {c : ℂ} (hc : ‖c‖ = 4) {r : ℝ} (hr : r ≤ 2) :
    closedBall c r ⊆ ball (0 : ℂ) 8
theorem isOpen_configY [T2Space X] : IsOpen (configY e)
theorem witness_mem_configY :
    e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4)) ∈ configY e ∧
      e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4)) ∈ configY e
theorem isConnected_configY [ConnectedSpace X] [T2Space X] : IsConnected (configY e)
theorem isPerronFamily_configFamily [T2Space X] : IsPerronFamily (configFamily e) (configY e)
theorem perronSup_ge_witness [T2Space X] :
    3 / 4 ≤ perronSup (configFamily e) (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4)))
theorem perronSup_le_witness [T2Space X] :
    perronSup (configFamily e) (e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) ≤ 1 / 4
```

Barrier functions are built inline (not exported): lower barrier
`if x ∈ e.source then max 0 ((log 2 − log‖e x − 4‖)/log 2) else 0`; upper barrier
`γ w = log‖w+4‖/log 2` compared via `SubMeanOn.le_of_frontier_le` on the annulus
`1 < ‖w+4‖ < 2`. Both use Mathlib's `AnalyticAt.harmonicAt_log_norm`.

## `Rado/Surface/Germs.lean`

Harmonic conjugates and the étale space — the key file for building holomorphic functions from harmonic ones.

```lean
def IsConjugate (u : X → ℝ) (F : X → ℂ) (V : Set X) : Prop :=
  HolomorphicOn F V ∧ ∀ x ∈ V, (F x).re = u x
```

```lean
theorem exists_conjugate {u : X → ℝ} {s : Set X} (hu : SurfaceHarmonicOn u s)
    (hs : IsOpen s) {x : X} (hx : x ∈ s) :
    ∃ V F, IsOpen V ∧ IsPreconnected V ∧ x ∈ V ∧ V ⊆ s ∧ IsConjugate u F V
theorem IsConjugate.eventuallyEq_add_const {u : X → ℝ} {F G : X → ℂ} {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hF : IsConjugate u F V) (hG : IsConjugate u G W)
    {y : X} (hyV : y ∈ V) (hyW : y ∈ W) : ∃ t : ℝ, F =ᶠ[𝓝 y] fun z ↦ G z + t * I
theorem IsConjugate.add_const_mul_I {u F V} (hF : IsConjugate u F V) (t : ℝ) :
    IsConjugate u (fun z ↦ F z + t * I) V
theorem IsConjugate.mono {u F V W} (hF : IsConjugate u F V) (hWV : W ⊆ V) : IsConjugate u F W
theorem IsConjugate.exists_sub_const {u F G V} (hV : IsOpen V) (hVc : IsPreconnected V)
    (hF : IsConjugate u F V) (hG : IsConjugate u G V) :
    ∃ t : ℝ, EqOn G (fun z ↦ F z + t * I) V
```

```lean
theorem SurfaceHarmonicOn.eqOn_const_of_locallyConstant {u : X → ℝ} {s : Set X}
    (hu : SurfaceHarmonicOn u s) (hs : IsOpen s) (hsc : IsPreconnected s) {y : X} (hy : y ∈ s)
    (hloc : ∀ᶠ z in 𝓝 y, u z = u y) : EqOn u (fun _ ↦ u y) s
```

Germ machinery and étale space (`variable (u : X → ℝ) (Y : Set X)`):

```lean
noncomputable def germValue {y : X} (γ : Germ (𝓝 y) ℂ) : ℂ := γ.liftOn (fun f ↦ f y) …
@[simp] theorem germValue_coe {y} (F : X → ℂ) : germValue (F : Germ (𝓝 y) ℂ) = F y
theorem isOpen_eventuallyEq_nhds {F G : X → ℂ} : IsOpen {x : X | F =ᶠ[𝓝 x] G}

def ConjEtale : Type _ :=
  {p : Σ y : X, Germ (𝓝 y) ℂ // p.1 ∈ Y ∧
    ∃ V F, IsOpen V ∧ p.1 ∈ V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ p.2 = (F : Germ (𝓝 p.1) ℂ)}
```

`namespace ConjEtale`:

```lean
def sheet (V : Set X) (F : X → ℂ) : Set (ConjEtale u Y) :=
  {q | q.1.1 ∈ V ∧ q.1.2 = (F : Germ (𝓝 q.1.1) ℂ)}
def basicSets : Set (Set (ConjEtale u Y)) :=
  {S | ∃ V F, IsOpen V ∧ IsPreconnected V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ S = sheet V F}
instance : TopologicalSpace (ConjEtale u Y) := TopologicalSpace.generateFrom (basicSets u Y)
def proj (q : ConjEtale u Y) : X := q.1.1
noncomputable def eval (q : ConjEtale u Y) : ℂ := germValue q.1.2
```

```lean
theorem mem_sheet_iff {V F q} : q ∈ sheet V F ↔ q.1.1 ∈ V ∧ q.1.2 = (F : Germ (𝓝 q.1.1) ℂ)
theorem isOpen_of_mem_basicSets {S} (hS : S ∈ basicSets u Y) : IsOpen S
theorem isTopologicalBasis_basicSets : TopologicalSpace.IsTopologicalBasis (basicSets u Y)
theorem continuous_proj : Continuous (proj (u := u) (Y := Y))
theorem isOpenMap_proj : IsOpenMap (proj (u := u) (Y := Y))
theorem injOn_proj_sheet {V F} : InjOn (proj (u := u) (Y := Y)) (sheet V F)
theorem t2Space [T2Space X] : T2Space (ConjEtale u Y)
theorem exists_mk (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y) {y : X} (hy : y ∈ Y) :
    ∃ q : ConjEtale u Y, proj q = y
theorem locallyCompactSpace [T2Space X] : LocallyCompactSpace (ConjEtale u Y)
theorem locallyConnectedSpace [T2Space X] : LocallyConnectedSpace (ConjEtale u Y)
theorem locally_secondCountable [T2Space X] (q : ConjEtale u Y) :
    ∃ U : Set (ConjEtale u Y), q ∈ U ∧ IsOpen U ∧ SecondCountableTopology U
theorem continuous_eval : Continuous (eval (u := u) (Y := Y))
theorem eval_discrete_fibers [T2Space X] (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y)
    (hYc : IsPreconnected Y) {x₀ x₁ : X} (h₀ : x₀ ∈ Y) (h₁ : x₁ ∈ Y)
    (hne : u x₀ ≠ u x₁) (q : ConjEtale u Y) :
    ∃ U ∈ 𝓝 q, ∀ w ∈ U, eval w = eval q → w = q
theorem surjOn_proj_connectedComponent [T2Space X] (hu : SurfaceHarmonicOn u Y)
    (hY : IsOpen Y) (hYc : IsPreconnected Y) (q₀ : ConjEtale u Y) :
    SurjOn (proj (u := u) (Y := Y)) (connectedComponent q₀) Y
```

## `Rado/Topology/SecondCountable.lean`

```lean
theorem IsCompact.secondCountableTopology {Z : Type*} [TopologicalSpace Z] {K : Set Z}
    (hK : IsCompact K)
    (hloc : ∀ z ∈ K, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ SecondCountableTopology U) :
    SecondCountableTopology K
theorem secondCountableTopology_of_countable_setCover {Z} {𝒰 : Set (Set Z)} (hct : 𝒰.Countable)
    (ho : ∀ U ∈ 𝒰, IsOpen U) (hsc : ∀ U ∈ 𝒰, SecondCountableTopology U) (hcov : ⋃₀ 𝒰 = univ) :
    SecondCountableTopology Z
theorem countable_of_pairwiseDisjoint_isOpen {Z} [SecondCountableTopology Z] {𝒰 : Set (Set Z)}
    (ho : ∀ U ∈ 𝒰, IsOpen U) (hne : ∀ U ∈ 𝒰, U.Nonempty) (hdisj : 𝒰.PairwiseDisjoint id) :
    𝒰.Countable
theorem countable_setOf_reflTransGen {α : Type*} {r : α → α → Prop} (a₀ : α)
    (h : ∀ a, {b | r a b}.Countable) : {b | Relation.ReflTransGen r a₀ b}.Countable
```

## `Rado/Topology/PoincareVolterra.lean`

```lean
theorem poincare_volterra {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z]
    [LocallyCompactSpace Z] [LocallyConnectedSpace Z]
    (hloc : ∀ z : Z, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ SecondCountableTopology U)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    {f : Z → Y} (hf : Continuous f)
    (hdisc : ∀ z : Z, ∃ U ∈ 𝓝 z, ∀ w ∈ U, f w = f z → w = z) :
    SecondCountableTopology Z
```

## `Rado/Surface/Assembly.lean` and `Rado/Main.lean`

```lean
theorem exists_config_chart [Nonempty X] : ∃ e ∈ riemannAtlas X, ball (0 : ℂ) 8 ⊆ e.target
theorem secondCountable_configY {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) (hb : ball (0 : ℂ) 8 ⊆ e.target) :
    SecondCountableTopology (configY e)
theorem secondCountableTopology_of_riemannSurface : SecondCountableTopology X
theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X
```

Assembly pipeline (inside `secondCountable_configY`): `Y = configY e`,
`u = perronSup (configFamily e)` harmonic and nonconstant (witness bounds), étale space
`ConjEtale u Y`, connected component `C`, `poincare_volterra` applied to `eval : C → ℂ`
(discrete fibers), descend along open surjective `proj : C → Y`.

## Notes for building Green's functions / biholomorphisms

- The Perron method is fully generic in `IsPerronFamily`/`perronSup`; for a Green's
  function define a new family (subharmonic, 0 near ∂, −log-pole cap) — replacement,
  Harnack, `surfaceHarmonicOn_perronSup` carry over. Mind the `Icc 0 1` bounds field.
- `poissonExtension_mem_Icc` gives max-principle bounds for normalization.
- `IsConjugate` + `ConjEtale` is exactly the apparatus for global conjugates / period
  analysis (monodromy = sheet structure; sheets differ by `+ t·I`).
- `HolomorphicOn` (surface) has identity theorem + chart independence.
- Only genuine `[T2Space X]` needs: replacement, configY openness, étale Hausdorff, assembly.
