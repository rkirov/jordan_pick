/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Collar

/-!
# Entering an end through its frontier circle (gap #2, interface layer)

`nonempty_simpleRayData` (`Fill/PolyRay.lean`) produces the escaping cutting ray of an end
`Z` starting from a point `z₀` in the **open** end.  `TubeData` (`Fill/RayBuild.lean`)
instead needs the ray edge `R` to satisfy `p ∈ R` and `R \ {p} ⊆ Z` with `p = γ 0` on the
frontier circle.  Bridging the two requires entering `Z` *through* `p`, which is what this
file supplies.

The lever is `exists_biholo_chart_germ` (`Surface/LevelChart.lean`): the exterior-disk
regularity hypothesis `hchart` hands us, at each frontier point, a chart `e` and a
holomorphic `F` with `Re F = f ∘ e.symm` and `deriv F ≠ 0`.  Promoting `F ∘ e` to a chart
`ψ` in `riemannAtlas X` gives a coordinate whose **real part is `f` itself**.  Since the
collar dichotomy (`Fill/Collar.lean`) says `V = {f > c}` near the frontier, `ψ` puts the
frontier into the half-plane normal form

* `V` ↔ `{Re > c}`,  `closure V` ↔ `{Re ≥ c}`,  `(closure V)ᶜ` ↔ `{Re < c}`,

on a small disk about `p`.  In that model entering the end is a straight leftward segment.

* `exists_halfdisk_chart` — the normal form;
* `halfdisk_image_subset_end` — the open left half-disk lands in the end `Z`;
* `halfdisk_end_eq` — in the model, `Z` *is* `{re < c}` and `frontier Z` *is* the diameter
  `{re = c}`;
* `exists_local_collar_of_halfdisk` — the ray edge and the two quarter-disk half-collars,
  supplying the set-level `TubeData` fields near `p`;
* `exists_boundary_entry_segment` — the straight chart segment from `p` into `Z`.

Note `exists_halfdisk_chart` needs **no** hypothesis on `frontier V` (in particular not
`hfc`): the collar dichotomy on the open set `A'` is enough, because the `closure V`
characterisation is proved directly from the model rather than through `collar_closure_ge`.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Half-disk normal form at a frontier point.**  Under the collar dichotomy
`x ∈ V ↔ c < f x` on an open `A' ∋ p` and the exterior-disk chart data at `p`, there is a
maximal-atlas chart `ψ` about `p` and a radius `r > 0` such that on `ball (ψ p) r`:

* the chart's real part *is* `f`, and `(ψ p).re = c`;
* `closure V` is exactly the closed half-disk `{c ≤ re}`.

So `(closure V)ᶜ` meets the disk in the open half-disk `{re < c}`, which is convex. -/
theorem exists_halfdisk_chart {V : Set X} {f : X → ℝ} {c : ℝ} {A' : Set X}
    (hA'o : IsOpen A') (hpos : ∀ x ∈ A', (x ∈ V ↔ c < f x))
    {p : X} (hpA' : p ∈ A') (hfp : f p = c)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X) (hpe : p ∈ e.source)
    {F : ℂ → ℂ} (hFan : AnalyticAt ℂ F (e p))
    (hFre : ∀ᶠ z in 𝓝 (e p), (F z).re = f (e.symm z))
    (hFd : deriv F (e p) ≠ 0) :
    ∃ ψ ∈ riemannAtlas X, ∃ r > 0, p ∈ ψ.source ∧ (ψ p).re = c ∧
      ball (ψ p) r ⊆ ψ.target ∧
      (∀ z ∈ ball (ψ p) r, ψ.symm z ∈ A' ∧ f (ψ.symm z) = z.re) ∧
      (∀ z ∈ ball (ψ p) r, (ψ.symm z ∈ closure V ↔ c ≤ z.re)) := by
  classical
  obtain ⟨ψ, hψ, hpψ, hψe, hψeq⟩ := exists_biholo_chart_germ he hpe hFan hFd
  obtain ⟨O, hOsub, hOo, hOmem⟩ := _root_.mem_nhds_iff.mp hFre
  have hesymm : e.symm (e p) = p := e.left_inv hpe
  have hψpre : (ψ p).re = c := by
    rw [hψeq p hpψ]
    have hO := hOsub hOmem
    simp only [mem_ofPred_eq] at hO
    rw [hO, hesymm, hfp]
  -- the good neighbourhood in `X`, pulled back to a ball in the chart
  set N : Set X := ψ.source ∩ A' ∩ (e.source ∩ e ⁻¹' O) with hNdef
  have hNo : IsOpen N :=
    (ψ.open_source.inter hA'o).inter (e.continuousOn.isOpen_inter_preimage e.open_source hOo)
  have hpN : p ∈ N := ⟨⟨hpψ, hpA'⟩, hpe, hOmem⟩
  have hopen : IsOpen (ψ.target ∩ ψ.symm ⁻¹' N) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target hNo
  have hmem : ψ p ∈ ψ.target ∩ ψ.symm ⁻¹' N := by
    refine ⟨ψ.map_source hpψ, ?_⟩
    simp only [mem_preimage, ψ.left_inv hpψ]
    exact hpN
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  -- on the ball the chart's real part is `f`
  have hfre : ∀ w ∈ ball (ψ p) r, f (ψ.symm w) = w.re := by
    intro w hw
    obtain ⟨hwtgt, hwN⟩ := hball hw
    have hFe : (F (e (ψ.symm w))).re = f (e.symm (e (ψ.symm w))) := hOsub hwN.2.2
    rw [e.left_inv hwN.2.1] at hFe
    rw [← hFe, ← hψeq _ (ψ.map_target hwtgt), ψ.right_inv hwtgt]
  have hA'mem : ∀ w ∈ ball (ψ p) r, ψ.symm w ∈ A' := fun w hw => (hball hw).2.1.2
  refine ⟨ψ, hψ, r, hr, hpψ, hψpre, fun z hz => (hball hz).1,
    fun z hz => ⟨hA'mem z hz, hfre z hz⟩, ?_⟩
  intro z hz
  obtain ⟨hztgt, hzN⟩ := hball hz
  constructor
  · -- `closure V` ⇒ `c ≤ re`: the open half-disk misses `V` entirely
    intro hcl
    by_contra hnle
    rw [not_le] at hnle
    set U : Set X := ψ.source ∩ ψ ⁻¹' (ball (ψ p) r ∩ {w : ℂ | w.re < c}) with hUdef
    have hUo : IsOpen U :=
      ψ.continuousOn.isOpen_inter_preimage ψ.open_source
        (isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const))
    have hUmem : ψ.symm z ∈ U := by
      refine ⟨ψ.map_target hztgt, ?_⟩
      simp only [mem_preimage, ψ.right_inv hztgt]
      exact ⟨hz, hnle⟩
    have hUV : U ∩ V = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨⟨hys, hymem⟩, hyV⟩
      simp only [mem_preimage] at hymem
      obtain ⟨hyb, hyre⟩ := hymem
      have hy' : ψ.symm (ψ y) = y := ψ.left_inv hys
      have hyA' : y ∈ A' := by have := hA'mem _ hyb; rwa [hy'] at this
      have hfy : f y = (ψ y).re := by have := hfre _ hyb; rwa [hy'] at this
      have hgt : c < f y := (hpos y hyA').mp hyV
      rw [hfy] at hgt
      exact absurd hgt (not_lt.mpr hyre.le)
    have := mem_closure_iff.mp hcl U hUo hUmem
    rw [hUV] at this
    exact absurd this Set.not_nonempty_empty
  · -- `c ≤ re` ⇒ `closure V`: interior points are in `V`, boundary points are limits of them
    intro hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- `z.re = c`: push slightly to the right, staying in the ball
      have hcont : ContinuousAt (ψ.symm) z :=
        ψ.continuousOn_symm.continuousAt (ψ.open_target.mem_nhds hztgt)
      have hbase : Filter.Tendsto (fun t : ℝ => z + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
        have hc : Continuous (fun t : ℝ => z + (t : ℂ)) :=
          continuous_const.add Complex.continuous_ofReal
        have h0 := hc.tendsto (0 : ℝ)
        simp only [Complex.ofReal_zero, add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto (hcont.tendsto.comp hbase) ?_
      filter_upwards [hbase (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with t hbt hpt
      simp only [Set.mem_Ioi] at hpt
      refine (hpos _ (hA'mem _ hbt)).mpr ?_
      rw [hfre _ hbt]
      simp only [Complex.add_re, Complex.ofReal_re, ← heq]
      linarith
    · exact subset_closure ((hpos _ (hA'mem z hz)).mpr (by rw [hfre z hz]; exact hlt))

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **The open half-disk of the normal form lies inside the end.**  It is convex, hence
connected; it misses `closure V`; and it meets the end `Z` because `p ∈ closure Z`.  So it
lies in `Z` rather than in some other component of `(closure V)ᶜ`. -/
theorem halfdisk_image_subset_end {V : Set X} {c : ℝ} {p x₀ : X}
    {ψ : OpenPartialHomeomorph X ℂ} {r : ℝ} (hr : 0 < r) (hpψ : p ∈ ψ.source)
    (hbtgt : ball (ψ p) r ⊆ ψ.target)
    (hclos : ∀ z ∈ ball (ψ p) r, (ψ.symm z ∈ closure V ↔ c ≤ z.re))
    (hpZ : p ∈ frontier (connectedComponentIn (closure V)ᶜ x₀)) :
    ψ.symm '' (ball (ψ p) r ∩ {u : ℂ | u.re < c}) ⊆
      connectedComponentIn (closure V)ᶜ x₀ := by
  classical
  set H : Set ℂ := ball (ψ p) r ∩ {u : ℂ | u.re < c} with hHdef
  have hHtgt : H ⊆ ψ.target := fun u hu => hbtgt hu.1
  have hHconn : IsPreconnected (ψ.symm '' H) :=
    ((convex_ball _ _).inter (convex_halfSpace_re_lt c)).isPreconnected.image _
      (ψ.continuousOn_symm.mono hHtgt)
  have hHcompl : ψ.symm '' H ⊆ (closure V)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    exact fun hcl => absurd ((hclos u hu.1).mp hcl) (not_le.mpr hu.2)
  -- `p ∈ closure Z`, so a chart-ball neighbourhood of `p` meets `Z`
  have hUo : IsOpen (ψ.source ∩ ψ ⁻¹' ball (ψ p) r) :=
    ψ.continuousOn.isOpen_inter_preimage ψ.open_source isOpen_ball
  have hpU : p ∈ ψ.source ∩ ψ ⁻¹' ball (ψ p) r := ⟨hpψ, mem_ball_self hr⟩
  obtain ⟨y, ⟨hys, hyb⟩, hyZ⟩ :=
    mem_closure_iff.mp (frontier_subset_closure hpZ) _ hUo hpU
  simp only [mem_preimage] at hyb
  have hy' : ψ.symm (ψ y) = y := ψ.left_inv hys
  have hyH : ψ y ∈ H := by
    refine ⟨hyb, ?_⟩
    have hycl : y ∉ closure V := connectedComponentIn_subset _ _ hyZ
    have hiff : y ∈ closure V ↔ c ≤ (ψ y).re := by
      have := hclos (ψ y) hyb; rwa [hy'] at this
    exact not_le.mp fun hle => hycl (hiff.mpr hle)
  rw [connectedComponentIn_eq hyZ]
  exact hHconn.subset_connectedComponentIn ⟨ψ y, hyH, hy'⟩ hHcompl

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **The end and its frontier, read off in the half-disk model.**  On the model disk the
end `Z` is exactly the open left half-disk `{re < c}` and `frontier Z` is exactly the
vertical diameter `{re = c}`.

The diameter statement is what the circle-edge termination of the half-collars needs: near
`p` the frontier circle `CZ` is a straight segment through `ψ p`, so cutting it at `p` into
the two arcs `Sm ∩ CZ` and `Sp ∩ CZ` is cutting the diameter into its two halves. -/
theorem halfdisk_end_eq {V : Set X} {c : ℝ} {p x₀ : X}
    {ψ : OpenPartialHomeomorph X ℂ} {r : ℝ} (hr : 0 < r) (hpψ : p ∈ ψ.source)
    (hbtgt : ball (ψ p) r ⊆ ψ.target)
    (hclos : ∀ z ∈ ball (ψ p) r, (ψ.symm z ∈ closure V ↔ c ≤ z.re))
    (hpZ : p ∈ frontier (connectedComponentIn (closure V)ᶜ x₀)) :
    (∀ z ∈ ball (ψ p) r,
      (ψ.symm z ∈ connectedComponentIn (closure V)ᶜ x₀ ↔ z.re < c)) ∧
    (∀ z ∈ ball (ψ p) r,
      (ψ.symm z ∈ frontier (connectedComponentIn (closure V)ᶜ x₀) ↔ z.re = c)) := by
  classical
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  set Z : Set X := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  have hZo : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  have hsub := halfdisk_image_subset_end hr hpψ hbtgt hclos hpZ
  -- the left half-disk is exactly `Z` inside the model disk
  have hZiff : ∀ z ∈ ball (ψ p) r, (ψ.symm z ∈ Z ↔ z.re < c) := by
    intro z hz
    constructor
    · intro hzZ
      exact not_le.mp fun hle =>
        (connectedComponentIn_subset _ _ hzZ) ((hclos z hz).mpr hle)
    · intro hlt
      exact hsub ⟨z, ⟨hz, hlt⟩, rfl⟩
  refine ⟨hZiff, fun z hz => ⟨fun hfr => ?_, fun hre => ?_⟩⟩
  · -- on the frontier: not in the open `Z`, and not strictly right of the diameter
    have hnZ : ψ.symm z ∉ Z := by rw [hZo.frontier_eq] at hfr; exact hfr.2
    have hle : c ≤ z.re := not_lt.mp fun h => hnZ ((hZiff z hz).mpr h)
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact heq.symm
    · -- strictly right of the diameter: an open neighbourhood misses `Z`
      exfalso
      set U : Set X := ψ.source ∩ ψ ⁻¹' (ball (ψ p) r ∩ {u : ℂ | c < u.re}) with hUdef
      have hUo : IsOpen U :=
        ψ.continuousOn.isOpen_inter_preimage ψ.open_source
          (isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop)))
      have hUmem : ψ.symm z ∈ U := by
        refine ⟨ψ.map_target (hbtgt hz), ?_⟩
        simp only [mem_preimage, ψ.right_inv (hbtgt hz)]
        exact ⟨hz, hlt⟩
      have hUZ : U ∩ Z = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro u ⟨⟨hus, humem⟩, huZ⟩
        simp only [mem_preimage] at humem
        have hu' : ψ.symm (ψ u) = u := ψ.left_inv hus
        have := (hZiff (ψ u) humem.1).mp (by rwa [hu'])
        exact absurd this (not_lt.mpr humem.2.le)
      have := mem_closure_iff.mp (frontier_subset_closure hfr) U hUo hUmem
      rw [hUZ] at this
      exact absurd this Set.not_nonempty_empty
  · -- on the diameter: not in `Z`, but a limit of points of `Z` from the left
    have hnZ : ψ.symm z ∉ Z := fun h => absurd ((hZiff z hz).mp h) (by rw [hre]; exact lt_irrefl c)
    have hztgt : z ∈ ψ.target := hbtgt hz
    have hcont : ContinuousAt (ψ.symm) z :=
      ψ.continuousOn_symm.continuousAt (ψ.open_target.mem_nhds hztgt)
    have hbase : Filter.Tendsto (fun t : ℝ => z - (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      have hc : Continuous (fun t : ℝ => z - (t : ℂ)) :=
        continuous_const.sub Complex.continuous_ofReal
      have h0 := hc.tendsto (0 : ℝ)
      simp only [Complex.ofReal_zero, sub_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hcl : ψ.symm z ∈ closure Z := by
      refine mem_closure_of_tendsto (hcont.tendsto.comp hbase) ?_
      filter_upwards [hbase (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with t hbt hpt
      simp only [Set.mem_Ioi] at hpt
      refine (hZiff _ hbt).mpr ?_
      simp only [Complex.sub_re, Complex.ofReal_re, hre]
      linarith
    rw [hZo.frontier_eq]
    exact ⟨hcl, hnZ⟩

/-- **The local two-sided collar at a frontier point.**  In the half-disk model the ray edge
`R` is the leftward radius and the two half-collars are the two quarter-disks below and
above it.  This supplies, on the model disk, the `TubeData` fields that constrain the sets:
`hpR`, `hRSm`, `hRSp`, `hRZ`, `hSmZ`, `hSpZ`, `hSmSp` and `hcovp`.

`Sm ∩ Sp = R` on the nose (not merely `⊆`), because `im ≤ y₀` and `y₀ ≤ im` intersect in
`im = y₀` and `ψ.symm` is injective on the chart target.  What is *not* here is anything
global: the ray leaves the model disk, and `Sm`/`Sp` must be continued along it. -/
theorem exists_local_collar_of_halfdisk [T2Space X] {V : Set X} {c : ℝ} {p x₀ : X}
    {ψ : OpenPartialHomeomorph X ℂ} {r : ℝ} (hr : 0 < r) (hpψ : p ∈ ψ.source)
    (hψpre : (ψ p).re = c)
    (hbtgt : ball (ψ p) r ⊆ ψ.target)
    (hclos : ∀ z ∈ ball (ψ p) r, (ψ.symm z ∈ closure V ↔ c ≤ z.re))
    (hpZ : p ∈ frontier (connectedComponentIn (closure V)ᶜ x₀)) :
    ∃ R Sm Sp : Set X,
      IsClosed R ∧ IsClosed Sm ∧ IsClosed Sp ∧
      p ∈ R ∧ R ⊆ Sm ∧ R ⊆ Sp ∧ Sm ∩ Sp = R ∧
      R \ {p} ⊆ connectedComponentIn (closure V)ᶜ x₀ ∧
      Sm ⊆ connectedComponentIn (closure V)ᶜ x₀ ∪
        frontier (connectedComponentIn (closure V)ᶜ x₀) ∧
      Sp ⊆ connectedComponentIn (closure V)ᶜ x₀ ∪
        frontier (connectedComponentIn (closure V)ᶜ x₀) ∧
      (∀ᶠ x in 𝓝 p, x ∈ connectedComponentIn (closure V)ᶜ x₀ → x ∈ Sm ∪ Sp) := by
  classical
  set Z : Set X := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  obtain ⟨hZiff, hFiff⟩ := halfdisk_end_eq hr hpψ hbtgt hclos hpZ
  set y₀ : ℝ := (ψ p).im with hy₀
  -- the model sets: a closed half-disk of radius `r/2`, split along the horizontal diameter
  set Kr : Set ℂ := closedBall (ψ p) (r / 2) ∩ {u : ℂ | u.re ≤ c} with hKr
  set MR : Set ℂ := Kr ∩ {u : ℂ | u.im = y₀} with hMR
  set Mm : Set ℂ := Kr ∩ {u : ℂ | u.im ≤ y₀} with hMm
  set Mp : Set ℂ := Kr ∩ {u : ℂ | y₀ ≤ u.im} with hMp
  have hKrball : Kr ⊆ ball (ψ p) r := fun u hu =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hu.1) (by linarith))
  have hKrtgt : Kr ⊆ ψ.target := hKrball.trans hbtgt
  have hKrc : IsCompact Kr :=
    (isCompact_closedBall _ _).inter_right (isClosed_le Complex.continuous_re continuous_const)
  have hcompact : ∀ M : Set ℂ, IsClosed M → IsCompact (ψ.symm '' (Kr ∩ M)) := fun M hM =>
    (hKrc.inter_right hM).image_of_continuousOn
      (ψ.continuousOn_symm.mono (fun u hu => hKrtgt hu.1))
  have hMRc : IsCompact (ψ.symm '' MR) := hcompact _ (isClosed_eq Complex.continuous_im continuous_const)
  have hMmc : IsCompact (ψ.symm '' Mm) := hcompact _ (isClosed_le Complex.continuous_im continuous_const)
  have hMpc : IsCompact (ψ.symm '' Mp) := hcompact _ (isClosed_le continuous_const Complex.continuous_im)
  -- `ψ p` is the unique point of `MR` on the diameter's right end
  have hpMR : ψ p ∈ MR := ⟨⟨mem_closedBall_self (by linarith), le_of_eq hψpre⟩, rfl⟩
  have hpsymm : ψ.symm (ψ p) = p := ψ.left_inv hpψ
  refine ⟨ψ.symm '' MR, ψ.symm '' Mm, ψ.symm '' Mp,
    hMRc.isClosed, hMmc.isClosed, hMpc.isClosed, ⟨ψ p, hpMR, hpsymm⟩,
    Set.image_mono (fun u hu => ⟨hu.1, le_of_eq hu.2⟩),
    Set.image_mono (fun u hu => ⟨hu.1, ge_of_eq hu.2⟩), ?_, ?_, ?_, ?_, ?_⟩
  · -- `Sm ∩ Sp = R`
    have hinj : Set.InjOn ψ.symm Kr :=
      ψ.symm.injOn.mono (by rw [ψ.symm_source]; exact hKrtgt)
    have hMeq : Mm ∩ Mp = MR := by
      ext u
      simp only [hMm, hMp, hMR, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hK, hle⟩, -, hge⟩; exact ⟨hK, le_antisymm hle hge⟩
      · rintro ⟨hK, heq⟩; exact ⟨⟨hK, le_of_eq heq⟩, hK, ge_of_eq heq⟩
    rw [← Set.InjOn.image_inter hinj (fun u hu => hu.1) (fun u hu => hu.1), hMeq]
  · -- `R \ {p} ⊆ Z`
    rintro _ ⟨⟨u, huMR, rfl⟩, hne⟩
    refine (hZiff u (hKrball huMR.1)).mpr ?_
    have hre : u.re ≤ c := by simpa using huMR.1.2
    rcases lt_or_eq_of_le hre with h | h
    · exact h
    · exact absurd (by rw [show u = ψ p from Complex.ext (h.trans hψpre.symm) huMR.2, hpsymm]; rfl)
        hne
  · -- `Sm ⊆ Z ∪ CZ`
    rintro _ ⟨u, ⟨hK, -⟩, rfl⟩
    have hre : u.re ≤ c := by simpa using hK.2
    rcases lt_or_eq_of_le hre with h | h
    · exact Or.inl ((hZiff u (hKrball hK)).mpr h)
    · exact Or.inr ((hFiff u (hKrball hK)).mpr h)
  · -- `Sp ⊆ Z ∪ CZ`
    rintro _ ⟨u, ⟨hK, -⟩, rfl⟩
    have hre : u.re ≤ c := by simpa using hK.2
    rcases lt_or_eq_of_le hre with h | h
    · exact Or.inl ((hZiff u (hKrball hK)).mpr h)
    · exact Or.inr ((hFiff u (hKrball hK)).mpr h)
  · -- near `p`, every point of `Z` is in one of the two quarter-disks
    have hUo : IsOpen (ψ.source ∩ ψ ⁻¹' ball (ψ p) (r / 2)) :=
      ψ.continuousOn.isOpen_inter_preimage ψ.open_source isOpen_ball
    have hpU : p ∈ ψ.source ∩ ψ ⁻¹' ball (ψ p) (r / 2) :=
      ⟨hpψ, mem_ball_self (by linarith)⟩
    filter_upwards [hUo.mem_nhds hpU] with x hx hxZ
    obtain ⟨hxs, hxb⟩ := hx
    simp only [mem_preimage] at hxb
    have hx' : ψ.symm (ψ x) = x := ψ.left_inv hxs
    have hxbr : ψ x ∈ ball (ψ p) r :=
      mem_ball.mpr (lt_trans (mem_ball.mp hxb) (by linarith))
    have hxlt : (ψ x).re < c := (hZiff (ψ x) hxbr).mp (by rwa [hx'])
    have hxK : ψ x ∈ Kr := ⟨ball_subset_closedBall hxb, hxlt.le⟩
    rcases le_total (ψ x).im y₀ with h | h
    · exact Or.inl ⟨ψ x, ⟨hxK, h⟩, hx'⟩
    · exact Or.inr ⟨ψ x, ⟨hxK, h⟩, hx'⟩

theorem exists_boundary_entry_segment {V : Set X} {f : X → ℝ} {c : ℝ} {A' : Set X}
    (hA'o : IsOpen A') (hpos : ∀ x ∈ A', (x ∈ V ↔ c < f x))
    {p : X} (hpA' : p ∈ A') (hfp : f p = c)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X) (hpe : p ∈ e.source)
    {F : ℂ → ℂ} (hFan : AnalyticAt ℂ F (e p))
    (hFre : ∀ᶠ z in 𝓝 (e p), (F z).re = f (e.symm z))
    (hFd : deriv F (e p) ≠ 0)
    {x₀ : X} (hpZ : p ∈ frontier (connectedComponentIn (closure V)ᶜ x₀)) :
    ∃ ψ ∈ riemannAtlas X, ∃ w : ℂ, p ∈ ψ.source ∧ w ≠ ψ p ∧
      segment ℝ (ψ p) w ⊆ ψ.target ∧
      ψ.symm '' (segment ℝ (ψ p) w \ {ψ p}) ⊆ connectedComponentIn (closure V)ᶜ x₀ := by
  classical
  obtain ⟨ψ, hψ, r, hr, hpψ, hψpre, hbtgt, hbA', hclos⟩ :=
    exists_halfdisk_chart hA'o hpos hpA' hfp he hpe hFan hFre hFd
  set Z : Set X := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  set H : Set ℂ := ball (ψ p) r ∩ {u : ℂ | u.re < c} with hHdef
  have hHZ : ψ.symm '' H ⊆ Z := halfdisk_image_subset_end hr hpψ hbtgt hclos hpZ
  -- the leftward radius
  have hwball : ψ p - ((r / 2 : ℝ) : ℂ) ∈ ball (ψ p) r := by
    rw [mem_ball, dist_eq_norm,
      show ψ p - ((r / 2 : ℝ) : ℂ) - ψ p = -((r / 2 : ℝ) : ℂ) by ring]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < r / 2)]
    linarith
  have hsegball : segment ℝ (ψ p) (ψ p - ((r / 2 : ℝ) : ℂ)) ⊆ ball (ψ p) r :=
    (convex_ball (ψ p) r).segment_subset (mem_ball_self hr) hwball
  refine ⟨ψ, hψ, ψ p - ((r / 2 : ℝ) : ℂ), hpψ, ?_, hsegball.trans hbtgt, ?_⟩
  · intro hcon
    have : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -hcon
    simp only [Complex.ofReal_eq_zero] at this
    linarith
  · rintro _ ⟨u, ⟨huseg, hune⟩, rfl⟩
    refine hHZ ⟨u, ⟨hsegball huseg, ?_⟩, rfl⟩
    · -- strict inequality: the only segment point with real part `c` is `ψ p`
      rw [segment_eq_image'] at huseg
      obtain ⟨θ, hθ, rfl⟩ := huseg
      simp only [sub_sub_cancel_left, mem_ofPred_eq, Complex.add_re, hψpre,
        Complex.smul_re, Complex.neg_re, Complex.ofReal_re, smul_eq_mul]
      have hθpos : 0 < θ := by
        rcases hθ.1.lt_or_eq with h | h
        · exact h
        · exact absurd (by simp [← h]) hune
      have : 0 < θ * (r / 2) := mul_pos hθpos (by linarith)
      linarith

end Uniformization
