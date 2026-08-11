/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.LevelRegular
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Local level-curve chart, frontier dichotomy and exterior disks (F3.c part 1)

This file upgrades `Uniformization.exists_harmonic_level_piece_regular`
(`LevelRegular.lean`, F3.b) with the **local structure of the level curve** at
every frontier point, in three layers.

## LAYER 1 — chart promotion (`exists_biholo_chart_germ`)

Given a maximal-atlas chart `e ∋ ξ` and a holomorphic `F : ℂ → ℂ` with
`deriv F (e ξ) ≠ 0`, the composite `F ∘ e` is (locally) a maximal-atlas chart:
`F` is a local biholomorphism (inverse-function theorem,
`HasStrictFDerivAt.toOpenPartialHomeomorph` + `AnalyticAt.analyticAt_localInverse`),
restricted to a ball where `F` and `F⁻¹` are analytic it lies in
`contDiffGroupoid 1`, and post-composition with `e` stays in the maximal atlas
(the argument of `Rado.affine_trans_mem_riemannAtlas`, with `F` for the affine
map).

## LAYER 2 + 3 — frontier dichotomy and exterior disks
(`level_frontier_dichotomy_ext`)

Abstract core, phrased purely from the *provenance* `V = fill cc` with
`cc = connectedComponentIn U₀ x₀`, `U₀ ⊆ {c < H}` (locally `= {c < H}`), plus a
chart `ψ` with `Re ψ = H` near a frontier point `ξ`.  In `ψ`-coordinates a small
ball splits along the line `{re = c}` into the `{c < H}`-half `Np` and the closed
`{H ≤ c}`-half `Nml`.

* Since `Nml ⊆ ccᶜ` is connected and contains `ξ`, and the `ξ`-component of `ccᶜ`
  is a component of `Vᶜ` (`connectedComponentIn_compl_fill`), we get `Nml ⊆ Vᶜ`.
* `Np` is preconnected inside `U₀`; if it missed `cc` then all of `N = Np ∪ Nml`
  would sit in `ccᶜ`, hence in `Vᶜ`, contradicting `ξ ∈ closure V`.  So
  `Np ⊆ cc ⊆ V`.

Hence near `ξ`, `x ∈ V ↔ c < H x` (the **dichotomy (v)**), and the exterior disk
tangent to `{re = c}` on the `{re < c}` side (in the chart `ψ` restricted to `N`)
witnesses `ExteriorDiskAt V ξ`.

## Final deliverable (`exists_level_piece_regular_frontier`)

`exists_harmonic_level_piece_regular` **re-assembled** with the two extra
conjuncts.  The re-assembly is verbatim (`LevelRegular.lean`'s private
`exists_annular_harmonic`/`midpt_dist` are copied — see the report), so that
`V = fill (connectedComponentIn U₀ x₀)` is in scope; the payload (iii) is fed to
LAYER 1 and then LAYER 2+3.  This makes the level piece satisfy **every** conjunct
of the frozen `exists_simply_connected_piece` except `IsSimplyConnected`.
-/

open Set Metric Topology InnerProductSpace Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## LAYER 1 — chart promotion -/

/-- **Chart promotion (germ form).**  If `e` is a maximal-atlas chart with
`ξ ∈ e.source` and `F : ℂ → ℂ` is analytic at `e ξ` with nonvanishing derivative
there, then `x ↦ F (e x)` is (on a neighbourhood of `ξ`) a maximal-atlas chart
`ψ`. -/
theorem exists_biholo_chart_germ {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X)
    {ξ : X} (hξe : ξ ∈ e.source) {F : ℂ → ℂ} (hFan : AnalyticAt ℂ F (e ξ))
    (hderiv : deriv F (e ξ) ≠ 0) :
    ∃ ψ ∈ riemannAtlas X, ξ ∈ ψ.source ∧ ψ.source ⊆ e.source ∧
      ∀ x ∈ ψ.source, ψ x = F (e x) := by
  classical
  set z₀ := e ξ with hz₀
  have hw0 : deriv F z₀ ≠ 0 := hderiv
  set i : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv F z₀) hw0) with hi
  have hfd : HasStrictFDerivAt F (i : ℂ →L[ℂ] ℂ) z₀ := hFan.hasStrictDerivAt
  set R : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph F with hR
  have hRcoe : ⇑R = F := hfd.toOpenPartialHomeomorph_coe
  have hz₀src : z₀ ∈ R.source := hfd.mem_toOpenPartialHomeomorph_source
  have hRz₀ : R z₀ = F z₀ := by rw [hRcoe]
  -- analyticity of the inverse near `F z₀`
  have hRsymm_an : AnalyticAt ℂ (⇑R.symm) (F z₀) := hFan.analyticAt_localInverse hderiv
  have hRsymm_ev : ∀ᶠ w in 𝓝 (F z₀), AnalyticAt ℂ (⇑R.symm) w := hRsymm_an.eventually_analyticAt
  obtain ⟨D, hDsub, hDo, hFz₀D⟩ := _root_.mem_nhds_iff.mp hRsymm_ev
  -- `R` is continuous at `z₀`, so `R⁻¹' D` is a neighbourhood
  have hRcont : ContinuousAt (⇑R) z₀ := R.continuousAt hz₀src
  have hpreD : (⇑R)⁻¹' D ∈ 𝓝 z₀ := by
    apply hRcont.preimage_mem_nhds
    rw [hRz₀]; exact hDo.mem_nhds hFz₀D
  have hFev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ F z := hFan.eventually_analyticAt
  have hOnhds : {z | AnalyticAt ℂ F z} ∩ R.source ∩ (⇑R)⁻¹' D ∈ 𝓝 z₀ :=
    inter_mem (inter_mem hFev (R.open_source.mem_nhds hz₀src)) hpreD
  obtain ⟨O, hOsub, hOo, hz₀O⟩ := _root_.mem_nhds_iff.mp hOnhds
  -- the restricted local biholomorphism
  set R' : OpenPartialHomeomorph ℂ ℂ := R.restrOpen O hOo with hR'
  have hR'src : R'.source = R.source ∩ O := rfl
  have hz₀R' : z₀ ∈ R'.source := ⟨hz₀src, hz₀O⟩
  have hR'coe : ⇑R' = F := by rw [hR', OpenPartialHomeomorph.coe_restrOpen, hRcoe]
  -- `R' ∈ contDiffGroupoid 1`
  have hR'mem : R' ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
    constructor
    · have hFO : AnalyticOnNhd ℂ F R'.source := fun z hz => (hOsub hz.2).1.1
      have : ContDiffOn ℂ 1 F R'.source := hFO.contDiffOn_of_completeSpace
      simpa [hR'coe] using this
    · have hR'tgt_sub : R'.target ⊆ D := by
        intro w hw
        have hw2 : w ∈ R.target ∩ R.symm ⁻¹' O := hw
        have hRsw : R.symm w ∈ O := hw2.2
        have : R (R.symm w) ∈ D := (hOsub hRsw).2
        rwa [R.right_inv hw2.1] at this
      have hSan : AnalyticOnNhd ℂ (⇑R.symm) R'.target := fun w hw => hDsub (hR'tgt_sub hw)
      have : ContDiffOn ℂ 1 (⇑R.symm) R'.target := hSan.contDiffOn_of_completeSpace
      simpa only [hR', OpenPartialHomeomorph.coe_restrOpen_symm] using this
  -- assemble `ψ = e.trans R'`, mimicking `affine_trans_mem_riemannAtlas`
  have he₀ : ∀ f ∈ atlas ℂ X, e.symm.trans f ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) ∧
      f.symm.trans e ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
    mem_maximalAtlas_iff.1 (IsManifold.mem_maximalAtlas_iff.1 he)
  refine ⟨e.trans R', ?_, ?_, ?_, ?_⟩
  · refine IsManifold.mem_maximalAtlas_iff.2 (mem_maximalAtlas_iff.2 fun f hf ↦ ⟨?_, ?_⟩)
    · have hrw : (e.trans R').symm.trans f = R'.symm.trans ((e.symm.trans f)) := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc]
      rw [hrw]
      exact (contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ)).trans
        ((contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ)).symm hR'mem) (he₀ f hf).1
    · have hrw : f.symm.trans (e.trans R') = (f.symm.trans e).trans R' :=
        (OpenPartialHomeomorph.trans_assoc _ _ _).symm
      rw [hrw]
      exact (contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ)).trans (he₀ f hf).2 hR'mem
  · rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hξe, ?_⟩
    rw [mem_preimage, ← hz₀]
    exact hz₀R'
  · rw [OpenPartialHomeomorph.trans_source]
    exact inter_subset_left
  · intro x hx
    rw [OpenPartialHomeomorph.trans_apply, hR'coe]

/-! ## LAYER 2 + 3 — the frontier dichotomy and exterior disk -/

/-- **Local dichotomy and exterior disk at a level-curve frontier point.**
For `V = fill (connectedComponentIn U₀ x₀)` with `U₀ ⊆ {c < H}` (and `= {c < H}`
locally, via `Uamb`), and a maximal-atlas chart `ψ` with `Re ψ = H` near a
frontier point `ξ` (`H ξ = c`), near `ξ` the piece is exactly the superlevel set
`{c < H}`, and `V` has an exterior disk at `ξ`. -/
theorem level_frontier_dichotomy_ext [T2Space X]
    {U₀ : Set X} (hU₀o : IsOpen U₀) {p : X} {H : X → ℝ} {c : ℝ}
    (hU₀H : ∀ x ∈ U₀, c < H x)
    {Uamb : Set X} (hUambo : IsOpen Uamb)
    (hsuper : ∀ x ∈ Uamb, c < H x → x ∈ U₀)
    {ξ : X}
    (hξfrV : ξ ∈ frontier (fill (connectedComponentIn U₀ p)))
    (hξUamb : ξ ∈ Uamb)
    {ψ : OpenPartialHomeomorph X ℂ} (hψ : ψ ∈ riemannAtlas X) (hξψ : ξ ∈ ψ.source)
    (hψH : ∀ᶠ x in 𝓝 ξ, (ψ x).re = H x)
    (hHξ : H ξ = c) :
    (∀ᶠ x in 𝓝 ξ, (x ∈ fill (connectedComponentIn U₀ p) ↔ c < H x)) ∧
      ExteriorDiskAt (fill (connectedComponentIn U₀ p)) ξ := by
  classical
  have : LocallyCompactSpace X := locallyCompactSpace
  have : LocallyConnectedSpace X := locallyConnectedSpace
  set cc := connectedComponentIn U₀ p with hccdef
  set V := fill cc with hVdef
  have hcco : IsOpen cc := hU₀o.connectedComponentIn
  have hVopen : IsOpen V := isOpen_fill hcco
  have hξnV : ξ ∉ V := by rw [hVopen.frontier_eq] at hξfrV; exact hξfrV.2
  have hξclV : ξ ∈ closure V := frontier_subset_closure hξfrV
  have hccU₀ : cc ⊆ U₀ := connectedComponentIn_subset _ _
  have hZsub : connectedComponentIn ccᶜ ξ ⊆ Vᶜ := by
    rw [← connectedComponentIn_compl_fill hξnV]; exact connectedComponentIn_subset _ _
  set q := ψ ξ with hqdef
  have hqre : q.re = c := by have h := hψH.self_of_nhds; rw [hqdef, h, hHξ]
  have hqtgt : q ∈ ψ.target := ψ.map_source hξψ
  have hsymmq : ψ.symm q = ξ := ψ.left_inv hξψ
  have hOnhds : {x | (ψ x).re = H x} ∩ ψ.source ∩ Uamb ∈ 𝓝 ξ :=
    inter_mem (inter_mem hψH (ψ.open_source.mem_nhds hξψ)) (hUambo.mem_nhds hξUamb)
  obtain ⟨O₀, hO₀sub, hO₀o, hξO₀⟩ := _root_.mem_nhds_iff.mp hOnhds
  have hpre : ψ.symm ⁻¹' O₀ ∩ ψ.target ∈ 𝓝 q :=
    inter_mem ((ψ.continuousAt_symm hqtgt).preimage_mem_nhds
      (by rw [hsymmq]; exact hO₀o.mem_nhds hξO₀)) (ψ.open_target.mem_nhds hqtgt)
  obtain ⟨ρ, hρpos, hballρ⟩ := Metric.mem_nhds_iff.mp hpre
  set B := ball q ρ with hBdef
  have hBtgt : B ⊆ ψ.target := fun w hw => (hballρ hw).2
  have hBsymm : ∀ w ∈ B, ψ.symm w ∈ O₀ := fun w hw => (hballρ hw).1
  set N := ψ.symm '' B with hNdef
  have hNopen : IsOpen N :=
    ψ.symm.isOpen_image_of_subset_source isOpen_ball
      (by rw [OpenPartialHomeomorph.symm_source]; exact hBtgt)
  have hξN : ξ ∈ N := ⟨q, mem_ball_self hρpos, hsymmq⟩
  have hNsubO₀ : N ⊆ O₀ := by rintro _ ⟨w, hw, rfl⟩; exact hBsymm w hw
  have hNUamb : N ⊆ Uamb := fun x hx => (hO₀sub (hNsubO₀ hx)).2
  have hsymmcontB : ContinuousOn ψ.symm B :=
    ψ.symm.continuousOn.mono (by rw [OpenPartialHomeomorph.symm_source]; exact hBtgt)
  have hNconn : IsPreconnected N := (convex_ball q ρ).isPreconnected.image _ hsymmcontB
  have hHsymm : ∀ w ∈ B, H (ψ.symm w) = w.re := by
    intro w hw
    have h : (ψ (ψ.symm w)).re = H (ψ.symm w) := (hO₀sub (hBsymm w hw)).1.1
    rw [ψ.right_inv (hBtgt hw)] at h
    exact h.symm
  have hlin : IsLinearMap ℝ (fun w : ℂ => w.re) := by
    constructor
    · intro a b; simp
    · intro r a; simp
  set Bp := B ∩ {w : ℂ | c < w.re} with hBpdef
  set Bml := B ∩ {w : ℂ | w.re ≤ c} with hBmldef
  have hBpconn : IsPreconnected Bp :=
    ((convex_ball q ρ).inter (convex_halfSpace_gt hlin c)).isPreconnected
  have hBmlconn : IsPreconnected Bml :=
    ((convex_ball q ρ).inter (convex_halfSpace_le hlin c)).isPreconnected
  set Np := ψ.symm '' Bp with hNpdef
  set Nml := ψ.symm '' Bml with hNmldef
  have hNpconn : IsPreconnected Np := hBpconn.image _ (hsymmcontB.mono inter_subset_left)
  have hNmlconn : IsPreconnected Nml := hBmlconn.image _ (hsymmcontB.mono inter_subset_left)
  have hNp_N : Np ⊆ N := Set.image_mono inter_subset_left
  have hNml_N : Nml ⊆ N := Set.image_mono inter_subset_left
  have hNp_lt : ∀ x ∈ Np, c < H x := by
    rintro x ⟨w, ⟨hwB, hwre⟩, rfl⟩; rw [hHsymm w hwB]; exact hwre
  have hNml_le : ∀ x ∈ Nml, H x ≤ c := by
    rintro x ⟨w, ⟨hwB, hwre⟩, rfl⟩; rw [hHsymm w hwB]; exact hwre
  have hmemNp : ∀ x ∈ N, c < H x → x ∈ Np := by
    rintro x ⟨w, hw, rfl⟩ hlt; rw [hHsymm w hw] at hlt; exact ⟨w, ⟨hw, hlt⟩, rfl⟩
  have hNsplit : N ⊆ Np ∪ Nml := by
    rintro x ⟨w, hw, rfl⟩
    rcases lt_or_ge c w.re with h | h
    · exact Or.inl ⟨w, ⟨hw, h⟩, rfl⟩
    · exact Or.inr ⟨w, ⟨hw, h⟩, rfl⟩
  have hξNml : ξ ∈ Nml := ⟨q, ⟨mem_ball_self hρpos, le_of_eq hqre⟩, hsymmq⟩
  have hNp_U₀ : Np ⊆ U₀ := fun x hx => hsuper x (hNUamb (hNp_N hx)) (hNp_lt x hx)
  have hNml_ccc : Nml ⊆ ccᶜ := by
    intro x hx hxcc
    exact absurd (hNml_le x hx) (not_le.mpr (hU₀H x (hccU₀ hxcc)))
  have hNml_Vc : Nml ⊆ Vᶜ :=
    (hNmlconn.subset_connectedComponentIn hξNml hNml_ccc).trans hZsub
  have hNp_cc : Np ⊆ cc := by
    by_cases hmeet : (Np ∩ cc).Nonempty
    · obtain ⟨a, haNp, hacc⟩ := hmeet
      have hacc2 : a ∈ connectedComponentIn U₀ p := hacc
      have h := hNpconn.subset_connectedComponentIn haNp hNp_U₀
      have hce : connectedComponentIn U₀ p = connectedComponentIn U₀ a :=
        connectedComponentIn_eq hacc2
      rw [← hce] at h
      exact h
    · exfalso
      rw [not_nonempty_iff_eq_empty] at hmeet
      have hNp_ccc : Np ⊆ ccᶜ := fun x hx hxcc =>
        Set.eq_empty_iff_forall_notMem.mp hmeet x ⟨hx, hxcc⟩
      have hN_ccc : N ⊆ ccᶜ := by
        intro x hx
        rcases hNsplit hx with h | h
        · exact hNp_ccc h
        · exact hNml_ccc h
      have hN_Vc : N ⊆ Vᶜ := (hNconn.subset_connectedComponentIn hξN hN_ccc).trans hZsub
      obtain ⟨y, hyN, hyV⟩ := _root_.mem_closure_iff.mp hξclV N hNopen hξN
      exact hN_Vc hyN hyV
  refine ⟨?_, ?_⟩
  · filter_upwards [hNopen.mem_nhds hξN] with x hx
    constructor
    · intro hxV
      rcases hNsplit hx with hp | hml
      · exact hNp_lt x hp
      · exact absurd hxV (hNml_Vc hml)
    · intro hlt
      exact subset_fill cc (hNp_cc (hmemNp x hx hlt))
  · set r := ρ / 3 with hrdef
    have hrpos : 0 < r := by positivity
    set c₀ : ℂ := q - (r : ℂ) with hc₀def
    set e' := ψ.restr N with he'def
    have he'src : e'.source = ψ.source ∩ N := ψ.restr_source' N hNopen
    have he'tgt : e'.target = ψ.target ∩ ψ.symm ⁻¹' N := by
      have h1 : e'.target = ψ.target ∩ ψ.symm ⁻¹' (interior N) :=
        PartialEquiv.restr_target ψ.toPartialEquiv (interior N)
      rwa [hNopen.interior_eq] at h1
    have he'coe : ⇑e' = ⇑ψ := rfl
    have he'mem : e' ∈ riemannAtlas X :=
      restr_mem_maximalAtlas (contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ)) hψ hNopen
    have hdist_lt : ∀ w : ℂ, w ∈ ball c₀ r → w.re < c := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      have h1 : |w.re - c₀.re| ≤ ‖w - c₀‖ := by
        have := Complex.abs_re_le_norm (w - c₀); simpa [Complex.sub_re] using this
      have hc₀re : c₀.re = c - r := by rw [hc₀def]; simp [hqre]
      have h2 : |w.re - (c - r)| < r := by rw [← hc₀re]; exact lt_of_le_of_lt h1 hw
      have h3 := (abs_lt.mp h2).2
      linarith
    refine ⟨e', he'mem, ?_, c₀, r, hrpos, ?_, ?_, ?_⟩
    · rw [he'src]; exact ⟨hξψ, hξN⟩
    · rw [he'tgt]
      intro w hw
      have hwB : w ∈ B := by
        rw [mem_closedBall, dist_eq_norm] at hw
        rw [hBdef, mem_ball, dist_eq_norm]
        have htri : ‖w - q‖ ≤ ‖w - c₀‖ + ‖c₀ - q‖ := by
          have := norm_add_le (w - c₀) (c₀ - q); simpa using this
        have hc₀q : ‖c₀ - q‖ = r := by
          rw [hc₀def]; simp [Complex.norm_real, abs_of_pos hrpos]
        rw [hc₀q] at htri
        calc ‖w - q‖ ≤ ‖w - c₀‖ + r := htri
          _ ≤ r + r := by linarith
          _ < ρ := by rw [hrdef]; linarith
      exact ⟨hBtgt hwB, by rw [mem_preimage]; exact ⟨w, hwB, rfl⟩⟩
    · have hxe : e' ξ = q := by rw [he'coe]
      rw [hxe, hc₀def, dist_eq_norm]
      simp [Complex.norm_real, abs_of_pos hrpos]
    · rintro x ⟨hxV, hxsrc⟩ hxball
      rw [he'src] at hxsrc
      have hxN : x ∈ N := hxsrc.2
      have hxNp : x ∈ Np := by
        rcases hNsplit hxN with hp | hml
        · exact hp
        · exact absurd hxV (hNml_Vc hml)
      have hlt : c < H x := hNp_lt x hxNp
      have hval : (ψ x).re = H x := (hO₀sub (hNsubO₀ hxN)).1.1
      have hre : (e' x).re < c := hdist_lt _ hxball
      rw [he'coe] at hre
      rw [hval] at hre
      linarith

/-! ## Copied private helpers from `LevelRegular.lean` (private there) -/

/-- Distances from the endpoints of a radius to its midpoint.  (Copied verbatim
from `LevelRegular.lean`, private there.) -/
private theorem midpt_dist' {a c : ℂ} {ρ : ℝ} (h : dist a c = ρ) :
    dist a ((a + c) / 2) = ρ / 2 ∧ dist ((a + c) / 2) c = ρ / 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  refine ⟨?_, ?_⟩
  · rw [dist_eq_norm, show a - (a + c) / 2 = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]
  · rw [dist_eq_norm, show (a + c) / 2 - c = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]

set_option maxHeartbeats 1200000 in
/-- Annular Dirichlet solution.  (Copied verbatim from `LevelRegular.lean`,
private there, with `midpt_dist` renamed `midpt_dist'`.) -/
private theorem exists_annular_harmonic' [T2Space X]
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
  have hintK₁_clW : ∀ x, x ∈ closure W → x ∉ interior K₁ := by
    have hsub : W ⊆ (interior K₁)ᶜ := fun x hx hxi => hx.2 (interior_subset hxi)
    intro x hx hxi
    exact (closure_minimal hsub isOpen_interior.isClosed_compl) hx hxi
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
  have hfrW_sub : ∀ ξ ∈ frontier W,
      ξ ∈ frontier U ∨ ∃ d ∈ disks, ξ ∈ d.circ := by
    intro ξ hξ
    rw [hWo.frontier_eq] at hξ
    obtain ⟨hξcl, hξW⟩ := hξ
    have hξclU : ξ ∈ closure U := hclW_U hξcl
    by_cases hξU : ξ ∈ U
    · have hξK₁ : ξ ∈ K₁ := by by_contra h; exact hξW ⟨hξU, h⟩
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
  have hregW : ∀ ξ ∈ frontier W, ExteriorDiskAt W ξ := by
    intro ξ hξ
    rcases hfrW_sub ξ hξ with hξU | ⟨d, hd, hξcirc⟩
    · obtain ⟨e', he', hξe', c, r, hr, hcb, hdist, hout⟩ := hreg ξ hξU
      exact ⟨e', he', hξe', c, r, hr, hcb, hdist, fun x hx => hout x ⟨hWU hx.1, hx.2⟩⟩
    · have hξs : ξ ∈ d.e.source := d.circ_subset_source hξcirc
      set a := d.e ξ with ha
      have hsphere : dist a d.c = d.ρ := (d.mem_circ_iff.mp hξcirc).2
      obtain ⟨hma, hmc⟩ := midpt_dist' hsphere
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

/-! ## The regular level-set piece with frontier structure -/

set_option maxHeartbeats 1600000 in
/-- **Regular harmonic level-set piece with frontier structure** (F3.c part 1).
As `exists_harmonic_level_piece_regular`, but additionally:

* **(v) local dichotomy** — near every frontier point `ξ`, `x ∈ V ↔ c < f x`;
* **exterior disks** — `ExteriorDiskAt V ξ` at every frontier point `ξ`.

Re-assembles the `LevelRegular.lean` construction (exposing `V = fill cc`) and
feeds the regular-value payload to LAYER 1 and LAYER 2+3 above. -/
theorem exists_level_piece_regular_frontier [T2Space X] [ConnectedSpace X]
    (hnc : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ (V : Set X) (f : X → ℝ) (c : ℝ) (A : Set X),
      IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
      (frontier V).Nonempty ∧
      (∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x)) ∧
      IsOpen A ∧ frontier V ⊆ A ∧ SurfaceHarmonicOn f A ∧
      (∀ ξ ∈ frontier V, f ξ = c) ∧
      (∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0) ∧
      (∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x)) ∧
      (∀ ξ ∈ frontier V, ExteriorDiskAt V ξ) := by
  classical
  have : LocallyCompactSpace X := locallyCompactSpace
  have : LocallyConnectedSpace X := locallyConnectedSpace
  have : SecondCountableTopology X := Rado.secondCountableTopology_of_riemannSurface
  obtain ⟨V₁, hV₁o, hV₁conn, hV₁cl, hKV₁, hx₀V₁, -, -, -⟩ := exists_regular_piece hnc hK hx₀
  set S : Set X := closure V₁ with hS_def
  have hScpt : IsCompact S := hV₁cl
  have hSconn : IsConnected S := hV₁conn.closure
  have hx₀S : x₀ ∈ S := subset_closure hx₀V₁
  have hKS : K ⊆ S := hKV₁.trans subset_closure
  obtain ⟨U, hUo, hUconn, hUcl, hSU, hx₀U, hfrU, hregU, -⟩ :=
    exists_regular_piece hnc hScpt hx₀S
  obtain ⟨disks, hdiskU, hScov⟩ := exists_disk_cover hScpt hUo hSU
  set K₁ : Set X := ⋃ d ∈ disks, d.disk with hK₁_def
  set W : Set X := U \ K₁ with hW_def
  have hK₁cl : IsClosed K₁ :=
    (disks.finite_toSet.isCompact_biUnion fun d _ => d.isCompact_disk).isClosed
  have hWo : IsOpen W := hUo.sdiff hK₁cl
  have hK₁U : K₁ ⊆ U := iUnion₂_subset hdiskU
  have hSK₁ : S ⊆ K₁ := hScov.trans (iUnion₂_mono fun d _ => d.odisk_subset_disk)
  have hKK₁ : K ⊆ K₁ := hKS.trans hSK₁
  obtain ⟨h, hharm, hcont, hIcc, hinner1, hfrU0⟩ :=
    exists_annular_harmonic' hUo hUcl hfrU hregU hdiskU
  set H : X → ℝ := fun x => if x ∈ K₁ then 1 else h x with hH_def
  have hHeqh : EqOn H h (closure W) := by
    intro x hx
    by_cases hxK₁ : x ∈ K₁
    · simp only [hH_def, if_pos hxK₁]
      have hxW : x ∉ W := fun hw => hw.2 hxK₁
      have hxfrW : x ∈ frontier W := by rw [hWo.frontier_eq]; exact ⟨hx, hxW⟩
      exact (hinner1 x hxfrW hxK₁).symm
    · simp only [hH_def, if_neg hxK₁]
  have hHcontU : ContinuousOn H U := by
    have hHK₁eq : EqOn H (fun _ => (1 : ℝ)) K₁ := fun x hx => by simp only [hH_def, if_pos hx]
    have h1 : ContinuousOn H (closure W ∪ K₁) :=
      ContinuousOn.union_of_isClosed (hcont.congr hHeqh)
        (continuousOn_const.congr hHK₁eq) isClosed_closure hK₁cl
    refine h1.mono fun x hx => ?_
    by_cases hxK₁ : x ∈ K₁
    · exact Or.inr hxK₁
    · exact Or.inl (subset_closure ⟨hx, hxK₁⟩)
  have hHW : SurfaceHarmonicOn H W := by
    intro e he z hz
    refine (harmonicAt_congr_nhds ?_).mpr (hharm e he z hz)
    filter_upwards [(isOpen_chartImage e hWo).mem_nhds hz] with w hw
    have hwW : e.symm w ∈ W := mapsTo_symm_chartImage hw
    simp only [Function.comp_apply, hH_def, if_neg hwW.2]
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
  have hWLind : IsLindelof W := HereditarilyLindelofSpace.isLindelof W
  set Uset : {y : X // y ∈ W} → Set X := fun i => PP i.1 with hUset_def
  have hUseto : ∀ i, IsOpen (Uset i) := fun i => hPPo i.1 i.2
  have hWcov : W ⊆ ⋃ i, Uset i := fun y hy =>
    mem_iUnion.mpr ⟨⟨y, hy⟩, hyPP y hy⟩
  obtain ⟨T, hTc, hTcov⟩ := hWLind.elim_countable_subcover Uset hUseto hWcov
  set CritVals : Set ℝ := ⋃ i ∈ T,
      (fun w => ((FF i.1 ∘ (chartAt ℂ i.1).symm) w).re) ''
        {w ∈ chartImage (chartAt ℂ i.1) (PP i.1) |
          deriv (FF i.1 ∘ (chartAt ℂ i.1).symm) w = 0} with hCrit_def
  have hCritCount : CritVals.Countable := by
    refine hTc.biUnion (fun i _ => ?_)
    exact countable_critical_values_patch
      (isOpen_chartImage _ (hPPo i.1 i.2)) (hPPprecon i.1 i.2) (hPPan i.1 i.2)
  obtain ⟨c, hcIoo, hc_notCrit⟩ := exists_radius_notMem hCritCount (show (0 : ℝ) < 1 by norm_num)
  have hc0 : (0 : ℝ) < c := hcIoo.1
  have hc1 : c < 1 := hcIoo.2
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
    have hnb : (𝓝[U₀] ξ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hξclU₀
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
  have hfrV : frontier V ⊆ frontier U₀ :=
    (frontier_fill_subset hcco).trans (frontier_connectedComponentIn_subset hU₀open)
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
      have hval : ((FF y ∘ e.symm) (e ξ)).re = c := by
        simp only [Function.comp_apply, hsymmξ]
        rw [hconj.2 ξ hξP]; exact hξc
      have hmem : c ∈ (fun w => ((FF y ∘ e.symm) w).re) ''
          {w ∈ chartImage e (PP y) | deriv (FF y ∘ e.symm) w = 0} :=
        ⟨e ξ, ⟨hξO, hderiv0⟩, hval⟩
      exact hc_notCrit (mem_iUnion₂.mpr ⟨i, hiT, hmem⟩)
  -- the two extra conjuncts, via LAYER 1 + LAYER 2+3
  have hextra : ∀ ξ ∈ frontier V,
      (∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < H x)) ∧ ExteriorDiskAt V ξ := by
    intro ξ hξ
    obtain ⟨e, he, hξe, F, hFan, hpayload, hderiv⟩ := hiii ξ hξ
    obtain ⟨ψ, hψ, hξψ, hψsrc, hψeq⟩ := exists_biholo_chart_germ he hξe hFan hderiv
    have hψH : ∀ᶠ x in 𝓝 ξ, (ψ x).re = H x := by
      have hpb : ∀ᶠ x in 𝓝 ξ, (F (e x)).re = H (e.symm (e x)) :=
        (e.continuousAt hξe).eventually hpayload
      filter_upwards [hpb, e.open_source.mem_nhds hξe, ψ.open_source.mem_nhds hξψ]
        with x hx hxe hxψ
      rw [hψeq x hxψ, hx, e.left_inv hxe]
    obtain ⟨hξW, hξc⟩ := hfrU₀ ξ (hfrV hξ)
    have hξU : ξ ∈ U := hξW.1
    have hU₀H : ∀ x ∈ U₀, c < H x := fun x hx => hx.2
    have hsuper : ∀ x ∈ U, c < H x → x ∈ U₀ := fun x hxU hxlt => ⟨hxU, hxlt⟩
    have hξ' : ξ ∈ frontier (fill (connectedComponentIn U₀ x₀)) := hξ
    exact level_frontier_dichotomy_ext (U₀ := U₀) (p := x₀)
      hU₀open hU₀H hUo hsuper hξ' hξU hψ hξψ hψH hξc
  refine ⟨V, H, c, W, isOpen_fill hcco, isConnected_fill hnc hcco hccconn,
    isCompact_closure_fill hnc hcco hcccl, (hKS.trans hSc).trans (subset_fill cc),
    nonempty_frontier_fill hnc hcco hcccl ⟨x₀, hx₀cc⟩,
    fun x hx => not_isCompact_connectedComponentIn_compl_fill hx,
    hWo, fun ξ hξ => (hfrU₀ ξ (hfrV hξ)).1, hHW,
    fun ξ hξ => (hfrU₀ ξ (hfrV hξ)).2, hiii,
    fun ξ hξ => (hextra ξ hξ).1, fun ξ hξ => (hextra ξ hξ).2⟩

end Uniformization
