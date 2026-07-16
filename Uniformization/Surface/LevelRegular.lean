/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Level
import Uniformization.Surface.Piece.Generic
import Rado.Surface.Germs
import Rado.Surface.Assembly

/-!
# Regular-value refinement of the harmonic level-set piece (W7 fallback F3, step F3.b)

This file upgrades `Uniformization.exists_harmonic_level_piece` (`Level.lean`,
F3.a) by choosing the level value `c` to be a **regular value** of the harmonic
function.  The upgraded theorem `exists_harmonic_level_piece_regular` delivers,
in addition to every conjunct of `exists_harmonic_level_piece`, the

**regular-value payload (iii):** at every frontier point `ξ` of the piece there
is a maximal-atlas chart `e ∋ ξ` and a *chart-representative* holomorphic
`F : ℂ → ℂ` with `Re (F z) = f (e.symm z)` near `e ξ` and **`deriv F (e ξ) ≠ 0`**
— i.e. `ξ` is not a critical point of `f`.  This is exactly the local
biholomorphism datum `F3.c` needs to give the level curve `{f = c}` its
implicit-function-theorem structure near the frontier.

## Route (the countable-exclusion core, no Sard)

The construction of `Level.lean` is *re-run* here (its private annular-Dirichlet
helper `exists_annular_harmonic` is copied verbatim, its public helper
`exists_disk_cover` is imported) so that we control the choice of `c`:

1. Build the annular harmonic function `H` on `W` (a copy of the F3.a assembly,
   independent of `c`).
2. **Critical values are countable.**  `X` is a connected Hausdorff Riemann
   surface, hence second countable (`Rado.secondCountableTopology_of_riemannSurface`),
   hence hereditarily Lindelöf.  Cover `W` by conjugate patches
   (`Rado.exists_conjugate`), each shrunk to a preconnected component inside a
   single chart; take a countable subcover.  On each patch the chart
   representative `G = F ∘ e.symm` is analytic on a preconnected open `O ⊆ ℂ`;
   its derivative `deriv G` is analytic, so by the principle of isolated zeros
   (`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`) either
   `G` is constant on `O` (one critical value) or the zero set of `deriv G` is
   discrete in `O` (`isDiscrete_of_codiscreteWithin`) hence countable
   (`IsLindelof.countable_of_isDiscrete`).  The image `Re G '' {deriv G = 0}` is
   therefore countable per patch, and countable over the countable subcover.
3. Pick `c ∈ (0,1)` avoiding this countable set (`exists_radius_notMem`).
4. Re-assemble the piece exactly as `Level.lean` does — every point-set
   conclusion transfers verbatim (the assembly uses only `0 < c < 1`).
5. At a frontier point `ξ`, `f ξ = c` is not a critical value, so the covering
   patch's chart representative at `ξ` has nonvanishing derivative: payload (iii).

## Cut

The *local sublevel relation* `∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ f x > c)`
(conjunct (iv) of the orchestrator's request) is **cut**.  It does not follow
naturally from (iii): near `ξ` the piece `V = fill (connectedComponentIn {H>c} x₀)`
need not agree with `{H > c}` (hole filling can add `{f < c}` lakes and the
connected-component selection can drop `{f > c}` regions not attached to `x₀`),
so relating `x ∈ V` to `f x > c` needs the global fill/component bookkeeping of
F3.c, not the local level-curve datum.  It is left to F3.c as directed.
-/

open Set Metric Topology InnerProductSpace Filter

namespace Uniformization

open Rado

/-! ## Countability of critical values on one conjugate patch (pure ℂ) -/

/-- On a preconnected open `O ⊆ ℂ`, for an analytic `G`, the set of *critical
values* `Re G '' {w ∈ O | deriv G w = 0}` is countable: either `deriv G` is
identically zero on `O` (so `G` is constant, one value) or its zeros are
discrete (`isDiscrete_of_codiscreteWithin`) hence countable in the hereditarily
Lindelöf space `ℂ`. -/
theorem countable_critical_values_patch {G : ℂ → ℂ} {O : Set ℂ}
    (hOo : IsOpen O) (hOc : IsPreconnected O) (hG : AnalyticOnNhd ℂ G O) :
    ((fun w => (G w).re) '' {w ∈ O | deriv G w = 0}).Countable := by
  have hderiv : AnalyticOnNhd ℂ (deriv G) O := hG.deriv
  rcases hderiv.eqOn_zero_or_eventually_ne_zero_of_preconnected hOc with hflat | hsharp
  · -- `G` is constant on `O`
    obtain ⟨a, ha⟩ := hOo.exists_is_const_of_deriv_eq_zero hOc hG.differentiableOn hflat
    refine (Set.countable_singleton a.re).mono ?_
    rintro _ ⟨w, ⟨hwO, -⟩, rfl⟩
    simp only [Set.mem_singleton_iff]
    rw [ha w hwO]
  · -- isolated zeros of `deriv G`
    have hsharp' : {w | deriv G w = 0}ᶜ ∈ Filter.codiscreteWithin O := by
      rw [compl_setOf]; exact hsharp
    have hdisc : IsDiscrete ({w | deriv G w = 0} ∩ O) := isDiscrete_of_codiscreteWithin hsharp'
    have hcount : ({w | deriv G w = 0} ∩ O).Countable :=
      (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
    have hset : {w ∈ O | deriv G w = 0} = {w | deriv G w = 0} ∩ O := by
      ext w; simp [and_comm]
    rw [hset]
    exact hcount.image _

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The annular Dirichlet solution (copied from `Level.lean`, private there) -/

/-- Distances from the endpoints of a radius to its midpoint. -/
private theorem midpt_dist {a c : ℂ} {ρ : ℝ} (h : dist a c = ρ) :
    dist a ((a + c) / 2) = ρ / 2 ∧ dist ((a + c) / 2) c = ρ / 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  refine ⟨?_, ?_⟩
  · rw [dist_eq_norm, show a - (a + c) / 2 = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]
  · rw [dist_eq_norm, show (a + c) / 2 - c = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]

set_option maxHeartbeats 1200000 in
/-- Dirichlet solution on the annular region `W = U \ K₁`, where `K₁` is a
finite union of closed chart disks seated in `U`: boundary data `1` on the inner
circles (`⊆ K₁`) and `0` on `frontier U`.  (Verbatim copy of `Level.lean`'s
private helper.) -/
private theorem exists_annular_harmonic [T2Space X]
    {U : Set X} (hUo : IsOpen U) (hUc : IsCompact (closure U))
    (hfr : (frontier U).Nonempty)
    (hreg : ∀ ξ ∈ frontier U, ExteriorDiskAt U ξ)
    {disks : Finset (ChartDisk X)} (hdisk : ∀ d ∈ disks, d.disk ⊆ U) :
    ∃ h : X → ℝ,
      SurfaceHarmonicOn h (U \ ⋃ d ∈ disks, d.disk) ∧
      ContinuousOn h (closure (U \ ⋃ d ∈ disks, d.disk)) ∧
      (∀ x ∈ closure (U \ ⋃ d ∈ disks, d.disk), h x ∈ Icc (0 : ℝ) 1) ∧
      (∀ ξ ∈ frontier (U \ ⋃ d ∈ disks, d.disk),
        ξ ∈ (⋃ d ∈ disks, d.disk) → h ξ = 1) ∧
      (∀ ξ ∈ frontier U, h ξ = 0) := by
  classical
  set K₁ : Set X := ⋃ d ∈ disks, d.disk with hK₁_def
  set W : Set X := U \ K₁ with hW_def
  have hK₁cpt : IsCompact K₁ := disks.finite_toSet.isCompact_biUnion fun d _ => d.isCompact_disk
  have hK₁cl : IsClosed K₁ := hK₁cpt.isClosed
  have hK₁U : K₁ ⊆ U := by
    rw [hK₁_def]; exact iUnion₂_subset hdisk
  have hWo : IsOpen W := hUo.sdiff hK₁cl
  have hWU : W ⊆ U := sdiff_subset
  have hclW_U : closure W ⊆ closure U := closure_mono hWU
  have hclW_cpt : IsCompact (closure W) := hUc.of_isClosed_subset isClosed_closure hclW_U
  -- `interior K₁` avoids `closure W`
  have hintK₁_clW : ∀ x, x ∈ closure W → x ∉ interior K₁ := by
    have hsub : W ⊆ (interior K₁)ᶜ := fun x hx hxi => hx.2 (interior_subset hxi)
    intro x hx hxi
    exact (closure_minimal hsub isOpen_interior.isClosed_compl) hx hxi
  -- `frontier U ⊆ frontier W`
  have hfrUnotU : ∀ ξ ∈ frontier U, ξ ∉ U := by
    intro ξ hξ; rw [frontier, hUo.interior_eq] at hξ; exact hξ.2
  have hfrU_sub : frontier U ⊆ frontier W := by
    intro ξ hξ
    have hξU : ξ ∉ U := hfrUnotU ξ hξ
    have hξK₁ : ξ ∉ K₁ := fun h => hξU (hK₁U h)
    rw [hWo.frontier_eq]
    refine ⟨?_, fun h => hξU h.1⟩
    rw [_root_.mem_closure_iff]
    intro o ho hξo
    have hξclU : ξ ∈ closure U := frontier_subset_closure hξ
    have h1 : ((o ∩ K₁ᶜ) ∩ U).Nonempty :=
      _root_.mem_closure_iff.mp hξclU _ (ho.inter hK₁cl.isOpen_compl) ⟨hξo, hξK₁⟩
    obtain ⟨y, ⟨hyo, hyK₁⟩, hyU⟩ := h1
    exact ⟨y, hyo, hyU, hyK₁⟩
  have hfrW_ne : (frontier W).Nonempty := hfr.imp fun ξ hξ => hfrU_sub hξ
  -- `frontier W ⊆ frontier U ∪ innerCirc`
  have hfrW_sub : ∀ ξ ∈ frontier W,
      ξ ∈ frontier U ∨ ∃ d ∈ disks, ξ ∈ d.circ := by
    intro ξ hξ
    rw [hWo.frontier_eq] at hξ
    obtain ⟨hξcl, hξW⟩ := hξ
    have hξclU : ξ ∈ closure U := hclW_U hξcl
    by_cases hξU : ξ ∈ U
    · -- inner: on a circle
      have hξK₁ : ξ ∈ K₁ := by by_contra h; exact hξW ⟨hξU, h⟩
      have hξni : ξ ∉ interior K₁ := hintK₁_clW ξ hξcl
      simp only [hK₁_def, mem_iUnion] at hξK₁
      obtain ⟨d, hd, hξd⟩ := hξK₁
      have hodi : d.odisk ⊆ interior K₁ :=
        d.isOpen_odisk.subset_interior_iff.mpr
          (d.odisk_subset_disk.trans (subset_biUnion_of_mem hd))
      have hξod : ξ ∉ d.odisk := fun h => hξni (hodi h)
      have : ξ ∈ d.circ := by
        rcases d.disk_eq_odisk_union_circ ▸ hξd with h | h
        · exact absurd h hξod
        · exact h
      exact Or.inr ⟨d, hd, this⟩
    · exact Or.inl (by rw [frontier, hUo.interior_eq]; exact ⟨hξclU, hξU⟩)
  -- exterior disk condition at every frontier point of `W`
  have hregW : ∀ ξ ∈ frontier W, ExteriorDiskAt W ξ := by
    intro ξ hξ
    rcases hfrW_sub ξ hξ with hξU | ⟨d, hd, hξcirc⟩
    · obtain ⟨e', he', hξe', c, r, hr, hcb, hdist, hout⟩ := hreg ξ hξU
      exact ⟨e', he', hξe', c, r, hr, hcb, hdist, fun x hx => hout x ⟨hWU hx.1, hx.2⟩⟩
    · -- internally tangent half-disk at an inner circle point
      have hξs : ξ ∈ d.e.source := d.circ_subset_source hξcirc
      set a := d.e ξ with ha
      have hsphere : dist a d.c = d.ρ := (d.mem_circ_iff.mp hξcirc).2
      obtain ⟨hma, hmc⟩ := midpt_dist hsphere
      have hρ := d.ρ_pos
      refine ⟨d.e, d.he, hξs, (a + d.c) / 2, d.ρ / 2, by positivity, ?_, hma, ?_⟩
      · refine subset_trans ?_ d.seated
        intro w hw
        rw [mem_closedBall] at hw ⊢
        calc dist w d.c ≤ dist w ((a + d.c) / 2) + dist ((a + d.c) / 2) d.c := dist_triangle _ _ _
          _ ≤ d.ρ / 2 + d.ρ / 2 := add_le_add hw hmc.le
          _ = d.ρ := by ring
      · rintro x ⟨hxW, hxs⟩ hxball
        rw [mem_ball] at hxball
        have hxod : x ∈ d.odisk := by
          refine d.mem_odisk_iff.mpr ⟨hxs, ?_⟩
          rw [mem_ball]
          calc dist (d.e x) d.c ≤ dist (d.e x) ((a + d.c) / 2) + dist ((a + d.c) / 2) d.c :=
                dist_triangle _ _ _
            _ < d.ρ / 2 + d.ρ / 2 := by linarith [hmc]
            _ = d.ρ := by ring
        exact hxW.2 (mem_biUnion hd (d.odisk_subset_disk hxod))
  -- boundary data: `1` on `K₁`, `0` elsewhere
  set fbd : X → ℝ := fun x => if x ∈ K₁ then 1 else 0 with hfbd_def
  have hfbd01 : ∀ ξ ∈ frontier W, fbd ξ ∈ Icc (0 : ℝ) 1 := by
    intro ξ _; by_cases h : ξ ∈ K₁ <;> simp [hfbd_def, h]
  have hfbdc : ContinuousOn fbd (frontier W) := by
    intro ξ hξ
    by_cases hξK₁ : ξ ∈ K₁
    · have hev : ∀ᶠ y in 𝓝[frontier W] ξ, fbd y = 1 := by
        filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds (hK₁U hξK₁)), self_mem_nhdsWithin]
          with y hyU hyfr
        rcases hfrW_sub y hyfr with hyfrU | ⟨d, hd, hyd⟩
        · exact absurd hyU (hfrUnotU y hyfrU)
        · exact if_pos (mem_biUnion hd (d.circ_subset_disk hyd))
      have hfξ : fbd ξ = 1 := if_pos hξK₁
      rw [ContinuousWithinAt, hfξ]
      exact Filter.Tendsto.congr' (by filter_upwards [hev] with y hy using hy.symm) tendsto_const_nhds
    · have hev : ∀ᶠ y in 𝓝[frontier W] ξ, fbd y = 0 := by
        filter_upwards [nhdsWithin_le_nhds (hK₁cl.isOpen_compl.mem_nhds hξK₁)] with y hyK₁
        exact if_neg hyK₁
      have hfξ : fbd ξ = 0 := if_neg hξK₁
      rw [ContinuousWithinAt, hfξ]
      exact Filter.Tendsto.congr' (by filter_upwards [hev] with y hy using hy.symm) tendsto_const_nhds
  -- solve the Dirichlet problem
  obtain ⟨u, huharm, hucont, hufr, huIcc⟩ :=
    exists_dirichlet_solution hWo hclW_cpt hfrW_ne hregW hfbdc
  have hne_im : (fbd '' frontier W).Nonempty := hfrW_ne.image fbd
  have hsInf0 : (0 : ℝ) ≤ sInf (fbd '' frontier W) := by
    refine le_csInf hne_im ?_
    rintro v ⟨ξ, hξ, rfl⟩; exact (hfbd01 ξ hξ).1
  have hsSup1 : sSup (fbd '' frontier W) ≤ 1 := by
    refine csSup_le hne_im ?_
    rintro v ⟨ξ, hξ, rfl⟩; exact (hfbd01 ξ hξ).2
  refine ⟨u, huharm, hucont, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := huIcc x hx
    exact ⟨le_trans hsInf0 h1, le_trans h2 hsSup1⟩
  · intro ξ hξ hξK₁
    rw [hufr hξ]; exact if_pos hξK₁
  · intro ξ hξ
    have hξfrW : ξ ∈ frontier W := hfrU_sub hξ
    have hξK₁ : ξ ∉ K₁ := fun h => hfrUnotU ξ hξ (hK₁U h)
    rw [hufr hξfrW]; exact if_neg hξK₁

/-! ## The regular harmonic level-set piece -/

set_option maxHeartbeats 1600000 in
/-- **Regular harmonic level-set piece** (W7 fallback F3.b).  As
`exists_harmonic_level_piece`, but the level value `c` is a *regular value*:
at every frontier point `ξ` the harmonic `f` has, in some maximal-atlas chart
`e ∋ ξ`, a holomorphic chart representative `F` with `Re F = f ∘ e.symm` near
`e ξ` and **`deriv F (e ξ) ≠ 0`** — the local-biholomorphism payload F3.c
consumes. -/
theorem exists_harmonic_level_piece_regular [T2Space X] [ConnectedSpace X]
    (hnc : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ (V : Set X) (f : X → ℝ) (c : ℝ) (A : Set X),
      IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
      (frontier V).Nonempty ∧
      (∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x)) ∧
      IsOpen A ∧ frontier V ⊆ A ∧ SurfaceHarmonicOn f A ∧
      (∀ ξ ∈ frontier V, f ξ = c) ∧
      (∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0) := by
  classical
  haveI : LocallyCompactSpace X := locallyCompactSpace
  haveI : LocallyConnectedSpace X := locallyConnectedSpace
  haveI : SecondCountableTopology X := Rado.secondCountableTopology_of_riemannSurface
  -- inner regular piece `V₁ ⊇ K`
  obtain ⟨V₁, hV₁o, hV₁conn, hV₁cl, hKV₁, hx₀V₁, -, -, -⟩ := exists_regular_piece hnc hK hx₀
  set S : Set X := closure V₁ with hS_def
  have hScpt : IsCompact S := hV₁cl
  have hSconn : IsConnected S := hV₁conn.closure
  have hx₀S : x₀ ∈ S := subset_closure hx₀V₁
  have hKS : K ⊆ S := hKV₁.trans subset_closure
  -- outer regular piece `U ⊇ S`
  obtain ⟨U, hUo, hUconn, hUcl, hSU, hx₀U, hfrU, hregU, -⟩ :=
    exists_regular_piece hnc hScpt hx₀S
  -- cover `S` by chart disks seated in `U`
  obtain ⟨disks, hdiskU, hScov⟩ := exists_disk_cover hScpt hUo hSU
  set K₁ : Set X := ⋃ d ∈ disks, d.disk with hK₁_def
  set W : Set X := U \ K₁ with hW_def
  have hK₁cl : IsClosed K₁ :=
    (disks.finite_toSet.isCompact_biUnion fun d _ => d.isCompact_disk).isClosed
  have hWo : IsOpen W := hUo.sdiff hK₁cl
  have hK₁U : K₁ ⊆ U := iUnion₂_subset hdiskU
  have hSK₁ : S ⊆ K₁ := hScov.trans (iUnion₂_mono fun d _ => d.odisk_subset_disk)
  have hKK₁ : K ⊆ K₁ := hKS.trans hSK₁
  -- annular harmonic solution
  obtain ⟨h, hharm, hcont, hIcc, hinner1, hfrU0⟩ :=
    exists_annular_harmonic hUo hUcl hfrU hregU hdiskU
  -- extend by `1` across `K₁`
  set H : X → ℝ := fun x => if x ∈ K₁ then 1 else h x with hH_def
  -- `H = h` on `closure W`
  have hHeqh : EqOn H h (closure W) := by
    intro x hx
    by_cases hxK₁ : x ∈ K₁
    · simp only [hH_def, if_pos hxK₁]
      have hxW : x ∉ W := fun hw => hw.2 hxK₁
      have hxfrW : x ∈ frontier W := by rw [hWo.frontier_eq]; exact ⟨hx, hxW⟩
      exact (hinner1 x hxfrW hxK₁).symm
    · simp only [hH_def, if_neg hxK₁]
  -- `H` continuous on `U`
  have hHcontU : ContinuousOn H U := by
    have hHK₁eq : EqOn H (fun _ => (1 : ℝ)) K₁ := fun x hx => by simp only [hH_def, if_pos hx]
    have h1 : ContinuousOn H (closure W ∪ K₁) :=
      ContinuousOn.union_of_isClosed (hcont.congr hHeqh)
        (continuousOn_const.congr hHK₁eq) isClosed_closure hK₁cl
    refine h1.mono fun x hx => ?_
    by_cases hxK₁ : x ∈ K₁
    · exact Or.inr hxK₁
    · exact Or.inl (subset_closure ⟨hx, hxK₁⟩)
  -- harmonicity of `H` on `W`
  have hHW : SurfaceHarmonicOn H W := by
    intro e he z hz
    refine (harmonicAt_congr_nhds ?_).mpr (hharm e he z hz)
    filter_upwards [(isOpen_chartImage e hWo).mem_nhds hz] with w hw
    have hwW : e.symm w ∈ W := mapsTo_symm_chartImage hw
    simp only [Function.comp_apply, hH_def, if_neg hwW.2]
  -- ===== regular-value selection =====
  -- conjugate patches: for each `y ∈ W`, a preconnected chart patch carrying a
  -- holomorphic conjugate `F` of `H` (`Re F = H`), analytic chart representative.
  have hpatch : ∀ y ∈ W, ∃ (F : X → ℂ) (P : Set X),
      IsOpen P ∧ y ∈ P ∧ P ⊆ W ∧ P ⊆ (chartAt ℂ y).source ∧
      IsPreconnected (chartImage (chartAt ℂ y) P) ∧
      IsConjugate H F P ∧
      AnalyticOnNhd ℂ (F ∘ (chartAt ℂ y).symm) (chartImage (chartAt ℂ y) P) := by
    intro y hy
    obtain ⟨V', F, hV'o, hV'c, hyV', hV'W, hFconj⟩ := exists_conjugate hHW hWo hy
    set e := chartAt ℂ y with he_def
    have hysrc : y ∈ e.source := mem_chart_source ℂ y
    set P := connectedComponentIn (V' ∩ e.source) y with hP_def
    have hPo : IsOpen P := (hV'o.inter e.open_source).connectedComponentIn
    have hyP : y ∈ P := mem_connectedComponentIn ⟨hyV', hysrc⟩
    have hPsub : P ⊆ V' ∩ e.source := connectedComponentIn_subset _ _
    have hPsrc : P ⊆ e.source := hPsub.trans inter_subset_right
    have hPV' : P ⊆ V' := hPsub.trans inter_subset_left
    have hPW : P ⊆ W := hPV'.trans hV'W
    have hPconn : IsPreconnected P := isPreconnected_connectedComponentIn
    have hCI : chartImage e P = e '' P := by
      simp only [Rado.chartImage, inter_eq_left.mpr hPsrc]
    have hCIprecon : IsPreconnected (chartImage e P) := by
      rw [hCI]; exact hPconn.image e (e.continuousOn.mono hPsrc)
    have hconjP : IsConjugate H F P := hFconj.mono hPV'
    have hanP : AnalyticOnNhd ℂ (F ∘ e.symm) (chartImage e P) := by
      intro w hw
      rw [hCI] at hw
      obtain ⟨x, hxP, rfl⟩ := hw
      exact hconjP.1.analyticAt_comp_symm (chartAt_mem_riemannAtlas y) ⟨hxP, hPsrc hxP⟩
    exact ⟨F, P, hPo, hyP, hPW, hPsrc, hCIprecon, hconjP, hanP⟩
  choose! FF PP hPPo hyPP hPPW hPPsrc hPPprecon hPPconj hPPan using hpatch
  -- countable subcover of `W` by patches
  have hWLind : IsLindelof W := HereditarilyLindelofSpace.isLindelof W
  set Uset : {y : X // y ∈ W} → Set X := fun i => PP i.1 with hUset_def
  have hUseto : ∀ i, IsOpen (Uset i) := fun i => hPPo i.1 i.2
  have hWcov : W ⊆ ⋃ i, Uset i := fun y hy =>
    mem_iUnion.mpr ⟨⟨y, hy⟩, hyPP y hy⟩
  obtain ⟨T, hTc, hTcov⟩ := hWLind.elim_countable_subcover Uset hUseto hWcov
  -- the critical values
  set CritVals : Set ℝ := ⋃ i ∈ T,
      (fun w => ((FF i.1 ∘ (chartAt ℂ i.1).symm) w).re) ''
        {w ∈ chartImage (chartAt ℂ i.1) (PP i.1) |
          deriv (FF i.1 ∘ (chartAt ℂ i.1).symm) w = 0} with hCrit_def
  have hCritCount : CritVals.Countable := by
    refine hTc.biUnion (fun i _ => ?_)
    exact countable_critical_values_patch
      (isOpen_chartImage _ (hPPo i.1 i.2)) (hPPprecon i.1 i.2) (hPPan i.1 i.2)
  -- pick a regular value `c ∈ (0,1)`
  obtain ⟨c, hcIoo, hc_notCrit⟩ := exists_radius_notMem hCritCount (show (0 : ℝ) < 1 by norm_num)
  have hc0 : (0 : ℝ) < c := hcIoo.1
  have hc1 : c < 1 := hcIoo.2
  -- ===== re-assemble the piece with the chosen `c` (as in `Level.lean`) =====
  set U₀ : Set X := U ∩ {x | c < H x} with hU₀_def
  have hU₀open : IsOpen U₀ := hHcontU.isOpen_inter_preimage hUo isOpen_Ioi
  have hU₀U : U₀ ⊆ U := inter_subset_left
  have hHK₁ : ∀ x ∈ K₁, H x = 1 := fun x hx => by simp only [hH_def, if_pos hx]
  have hSU₀ : S ⊆ U₀ := by
    intro x hx
    exact ⟨hSU hx, show c < H x by rw [hHK₁ x (hSK₁ hx)]; exact hc1⟩
  have hx₀U₀ : x₀ ∈ U₀ := hSU₀ hx₀S
  set cc : Set X := connectedComponentIn U₀ x₀ with hcc_def
  have hcco : IsOpen cc := hU₀open.connectedComponentIn
  have hccconn : IsConnected cc := isConnected_connectedComponentIn_iff.mpr hx₀U₀
  have hx₀cc : x₀ ∈ cc := mem_connectedComponentIn hx₀U₀
  have hccU₀ : cc ⊆ U₀ := connectedComponentIn_subset _ _
  have hSc : S ⊆ cc := hSconn.isPreconnected.subset_connectedComponentIn hx₀S hSU₀
  have hcccl : IsCompact (closure cc) :=
    hUcl.of_isClosed_subset isClosed_closure (closure_mono (hccU₀.trans hU₀U))
  set V : Set X := fill cc with hV_def
  -- frontier points of `U` are not in `closure U₀` (there `h → 0 < c`)
  have hfrUnotcl : ∀ ξ ∈ frontier U, ξ ∉ closure U₀ := by
    intro ξ hξ hcl
    have hξnU : ξ ∉ U := by rw [frontier, hUo.interior_eq] at hξ; exact hξ.2
    have hξK₁ : ξ ∉ K₁ := fun hh => hξnU (hK₁U hh)
    have hξclW : ξ ∈ closure W := by
      rw [_root_.mem_closure_iff]
      intro o ho hξo
      have hξclU : ξ ∈ closure U := frontier_subset_closure hξ
      obtain ⟨z, ⟨hzo, hzK₁⟩, hzU⟩ :=
        _root_.mem_closure_iff.mp hξclU _ (ho.inter hK₁cl.isOpen_compl) ⟨hξo, hξK₁⟩
      exact ⟨z, hzo, hzU, hzK₁⟩
    have hhξ : h ξ = 0 := hfrU0 ξ hξ
    have hcwa : Filter.Tendsto h (𝓝[closure W] ξ) (𝓝 (h ξ)) := hcont ξ hξclW
    rw [hhξ] at hcwa
    have hev : {y | h y < c} ∈ 𝓝[closure W] ξ := hcwa (Iio_mem_nhds hc0)
    obtain ⟨O, hOo, hξO, hOsub⟩ := mem_nhdsWithin.mp hev
    obtain ⟨y, ⟨hyO, hyK₁⟩, hyU₀⟩ :=
      _root_.mem_closure_iff.mp hcl (O ∩ K₁ᶜ) (hOo.inter hK₁cl.isOpen_compl) ⟨hξO, hξK₁⟩
    have hyW : y ∈ W := ⟨hyU₀.1, hyK₁⟩
    have hyHh : H y = h y := by simp only [hH_def, if_neg hyK₁]
    have hylt : h y < c := hOsub ⟨hyO, subset_closure hyW⟩
    have hlt2 : c < H y := hyU₀.2
    rw [hyHh] at hlt2
    linarith
  -- `frontier U₀ ⊆ W ∩ {H = c}`
  have hfrU₀ : ∀ ξ ∈ frontier U₀, ξ ∈ W ∧ H ξ = c := by
    intro ξ hξ
    have hξclU₀ : ξ ∈ closure U₀ := frontier_subset_closure hξ
    have hξnU₀ : ξ ∉ U₀ := by
      have := hξ.2; rwa [hU₀open.interior_eq] at this
    have hξclU : ξ ∈ closure U := closure_mono hU₀U hξclU₀
    have hξU : ξ ∈ U := by
      by_cases hU : ξ ∈ U
      · exact hU
      · exact absurd hξclU₀
          (hfrUnotcl ξ (by rw [frontier, hUo.interior_eq]; exact ⟨hξclU, hU⟩))
    haveI hnb : (𝓝[U₀] ξ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hξclU₀
    have htend : Filter.Tendsto H (𝓝[U₀] ξ) (𝓝 (H ξ)) := (hHcontU ξ hξU).mono hU₀U
    have hge : c ≤ H ξ := by
      refine ge_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin] with y hy using le_of_lt hy.2
    have hle : H ξ ≤ c := by
      by_contra hlt; exact hξnU₀ ⟨hξU, not_le.mp hlt⟩
    have hHξc : H ξ = c := le_antisymm hle hge
    have hξK₁ : ξ ∉ K₁ := by
      intro hh; rw [hHK₁ ξ hh] at hHξc; linarith
    exact ⟨⟨hξU, hξK₁⟩, hHξc⟩
  -- `frontier V ⊆ frontier U₀`
  have hfrV : frontier V ⊆ frontier U₀ :=
    (frontier_fill_subset hcco).trans (frontier_connectedComponentIn_subset hU₀open)
  -- ===== the regular-value payload (iii) =====
  have hiii : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
        (∀ᶠ z in 𝓝 (e ξ), (F z).re = H (e.symm z)) ∧ deriv F (e ξ) ≠ 0 := by
    intro ξ hξ
    obtain ⟨hξW, hξc⟩ := hfrU₀ ξ (hfrV hξ)
    obtain ⟨i, hiT, hξP⟩ := mem_iUnion₂.mp (hTcov hξW)
    set y := i.1 with hy_def
    have hyW : y ∈ W := i.2
    set e := chartAt ℂ y with he_def
    have hPsrc : PP y ⊆ e.source := hPPsrc y hyW
    have hconj : IsConjugate H (FF y) (PP y) := hPPconj y hyW
    have hanO : AnalyticOnNhd ℂ (FF y ∘ e.symm) (chartImage e (PP y)) := hPPan y hyW
    have hOopen : IsOpen (chartImage e (PP y)) := isOpen_chartImage e (hPPo y hyW)
    have hξsrc : ξ ∈ e.source := hPsrc hξP
    have hξO : e ξ ∈ chartImage e (PP y) := mem_chartImage_of_mem hξP hξsrc
    have hsymmξ : e.symm (e ξ) = ξ := e.left_inv hξsrc
    refine ⟨e, chartAt_mem_riemannAtlas y, hξsrc, FF y ∘ e.symm, hanO _ hξO, ?_, ?_⟩
    · filter_upwards [hOopen.mem_nhds hξO] with z hz
      have hzP : e.symm z ∈ PP y := mapsTo_symm_chartImage hz
      exact hconj.2 _ hzP
    · intro hderiv0
      -- else `c = H ξ` would be a critical value
      have hval : ((FF y ∘ e.symm) (e ξ)).re = c := by
        simp only [Function.comp_apply, hsymmξ]
        rw [hconj.2 ξ hξP]; exact hξc
      have hmem : c ∈ (fun w => ((FF y ∘ e.symm) w).re) ''
          {w ∈ chartImage e (PP y) | deriv (FF y ∘ e.symm) w = 0} :=
        ⟨e ξ, ⟨hξO, hderiv0⟩, hval⟩
      exact hc_notCrit (mem_iUnion₂.mpr ⟨i, hiT, hmem⟩)
  -- assemble
  refine ⟨V, H, c, W, isOpen_fill hcco, isConnected_fill hnc hcco hccconn,
    isCompact_closure_fill hnc hcco hcccl, (hKS.trans hSc).trans (subset_fill cc),
    nonempty_frontier_fill hnc hcco hcccl ⟨x₀, hx₀cc⟩,
    fun x hx => not_isCompact_connectedComponentIn_compl_fill hx,
    hWo, fun ξ hξ => (hfrU₀ ξ (hfrV hξ)).1, hHW,
    fun ξ hξ => (hfrU₀ ξ (hfrV hξ)).2, hiii⟩

end Uniformization
