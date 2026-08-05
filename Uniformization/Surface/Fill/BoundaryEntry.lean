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
    simp only [mem_setOf_eq] at hO
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

/-- **Straight chart segment entering an end through a frontier point.**  If `p` lies on the
frontier of the end `Z = connectedComponentIn (closure V)ᶜ x₀` and carries the exterior-disk
chart data, then some maximal-atlas chart `ψ` about `p` admits a nondegenerate straight
segment from `ψ p` whose image, *punctured at `p`*, lies in `Z`.

This is exactly the ray edge `R` that `TubeData` requires near its base point: `p ∈ R` with
`R \ {p} ⊆ Z`.  In the half-plane model of `exists_halfdisk_chart` the segment is the
leftward radius `[ψ p, ψ p − r/2]`; the punctured part has real part `< c`, hence misses
`closure V`, and lands in `Z` rather than some other component because the whole open
half-disk is connected and meets `Z` (as `p ∈ closure Z`). -/
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
  -- the open half-disk, and its image in `X`
  set H : Set ℂ := ball (ψ p) r ∩ {u : ℂ | u.re < c} with hHdef
  have hHtgt : H ⊆ ψ.target := fun u hu => hbtgt hu.1
  have hHconv : Convex ℝ H :=
    (convex_ball _ _).inter (convex_halfSpace_re_lt c)
  have hHconn : IsPreconnected (ψ.symm '' H) :=
    hHconv.isPreconnected.image _ (ψ.continuousOn_symm.mono hHtgt)
  have hHcompl : ψ.symm '' H ⊆ (closure V)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    exact fun hcl => absurd ((hclos u hu.1).mp hcl) (not_le.mpr hu.2)
  -- `p ∈ closure Z`, so a chart-ball neighbourhood of `p` meets `Z`
  have hpcl : p ∈ closure Z := (frontier_subset_closure hpZ)
  have hUo : IsOpen (ψ.source ∩ ψ ⁻¹' ball (ψ p) r) :=
    ψ.continuousOn.isOpen_inter_preimage ψ.open_source isOpen_ball
  have hpU : p ∈ ψ.source ∩ ψ ⁻¹' ball (ψ p) r := ⟨hpψ, mem_ball_self hr⟩
  obtain ⟨y, ⟨hys, hyb⟩, hyZ⟩ := mem_closure_iff.mp hpcl _ hUo hpU
  simp only [mem_preimage] at hyb
  have hy' : ψ.symm (ψ y) = y := ψ.left_inv hys
  have hyH : ψ y ∈ H := by
    refine ⟨hyb, ?_⟩
    have hycl : y ∉ closure V := connectedComponentIn_subset _ _ hyZ
    have hiff : y ∈ closure V ↔ c ≤ (ψ y).re := by
      have := hclos (ψ y) hyb; rwa [hy'] at this
    exact not_le.mp fun hle => hycl (hiff.mpr hle)
  have hymem : y ∈ ψ.symm '' H := ⟨ψ y, hyH, hy'⟩
  -- the half-disk image is connected, sits in the complement, and meets `Z`
  have hHZ : ψ.symm '' H ⊆ Z := by
    rw [hZdef, connectedComponentIn_eq hyZ]
    exact hHconn.subset_connectedComponentIn hymem hHcompl
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
      simp only [sub_sub_cancel_left, mem_setOf_eq, Complex.add_re, hψpre,
        Complex.smul_re, Complex.neg_re, Complex.ofReal_re, smul_eq_mul]
      have hθpos : 0 < θ := by
        rcases hθ.1.lt_or_eq with h | h
        · exact h
        · exact absurd (by simp [← h]) hune
      have : 0 < θ * (r / 2) := mul_pos hθpos (by linarith)
      linarith

end Uniformization
