/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Ends
import Uniformization.Surface.Fill.CircleParam
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Metrizable.Urysohn

/-!
# The Tietze ray-collar collapse of one complement end (W7 step L5.5–L6, part B)

This file isolates the *analytic packaging* of the Anghel–Stan per-end collapse.
The geometric construction of the cutting ray and its two-sided collar (part A) is
abstracted into a structure `RayCollar`; given such a datum, `collapse_of_rayCollar`
produces the continuous collapse map `h : C(X, X)` fixing everything outside the end
`Z` and mapping `Z` into `closure V`.

The mathematical content:

* the frontier circle `CZ = frontier Z` is parametrised by a `1`-periodic `γ` with
  `range γ = CZ` and `γ` injective on `Ico 0 1`; the **angular coordinate**
  `θ = invFunOn γ (Ico 0 1)` is continuous on `CZ ∖ {p}` (`exists_angle`, a
  sequential-compactness argument using metrizability);
* the end is cut along a ray `R` flanked by two **corner-matched half-collars**
  `Sm, Sp` (closed sets meeting only along `R`) carrying continuous collar
  coordinates `dm, dp` that equal `0`/`1` on the ray and match `θ` at the circle
  edge; the angular data (`θ` on the big arc, `dm` on `Sm`, `dp` on `Sp`) is
  continuous on a closed subset of the open subspace `Y = (Z ∪ CZ) ∖ R`, is
  Tietze-extended, and precomposed with `γ`;
* the resulting `Ψ` is continuous across the ray (periodicity `γ 1 = γ 0 = p`
  heals the angular jump) and equals the identity on `CZ`, so it glues with the
  identity outside `Z` into the collapse `h`.

The corner matching is essential: a naive "two open sides with data `0`/`1`" datum
is *unsatisfiable* (the sides' closures cannot avoid `CZ ∖ {p}` while covering the
`Z`-side near `p`), so the collar coordinates must interpolate continuously from the
ray value to the angular value `θ` along the circle edge.

The reduction `exists_end_collapse_of_rayCollar` shows that a supply of `RayCollar`
data for every end discharges `exists_end_collapse` (the project's remaining sorry).
-/

open Set Topology Filter TopologicalSpace

namespace Uniformization

open Rado

/-! ## The angular coordinate is continuous off the base point -/

/-- **Continuity of the angular coordinate.**  For a `1`-periodic parametrisation
`γ` of a topological circle `CZ = range γ`, injective on `Ico 0 1` with base point
`p = γ 0`, the inverse `θ = invFunOn γ (Ico 0 1)` is a genuine coordinate on
`CZ ∖ {p}`: `γ (θ x) = x`, `θ x ∈ Ioo 0 1`, and `θ` is continuous there.  The
continuity is a sequential-compactness argument: any sequence `xₙ → x₀` in
`CZ ∖ {p}` has parameters `sₙ = θ xₙ ∈ (0,1)`; every subsequential limit `a` of the
bounded `sₙ` satisfies `γ a = x₀ = γ (θ x₀)`, hence `a = θ x₀` by injectivity, so
`sₙ → θ x₀`. -/
theorem exists_angle {X : Type*} [TopologicalSpace X] [T2Space X] [MetrizableSpace X]
    {CZ : Set X} {γ : ℝ → X} {p : X}
    (hγc : Continuous γ) (hγp : Function.Periodic γ 1)
    (hγr : Set.range γ = CZ) (hγi : Set.InjOn γ (Set.Ico (0 : ℝ) 1)) (hp : γ 0 = p) :
    ∃ θ : X → ℝ,
      (∀ x ∈ CZ \ {p}, γ (θ x) = x ∧ θ x ∈ Set.Ioo (0 : ℝ) 1) ∧
      ContinuousOn θ (CZ \ {p}) := by
  classical
  set θ : X → ℝ := Function.invFunOn γ (Set.Ico (0 : ℝ) 1) with hθdef
  -- `γ 1 = p`
  have hγ1 : γ 1 = p := by
    have h := hγp 0; rw [zero_add] at h; rw [h, hp]
  -- basic value property of `θ`
  have hval : ∀ x ∈ CZ \ {p}, γ (θ x) = x ∧ θ x ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro x ⟨hxCZ, hxp⟩
    rw [← hγr] at hxCZ
    obtain ⟨t, rfl⟩ := hxCZ
    obtain ⟨y, hyIco, hxy⟩ := hγp.exists_mem_Ico₀ (by norm_num) t
    -- `γ t = γ y`, `y ∈ Ico 0 1`
    have hθeq : θ (γ t) = y := by
      rw [hθdef, hxy]
      exact hγi.leftInvOn_invFunOn hyIco
    refine ⟨by rw [hθeq, ← hxy], ?_⟩
    rw [hθeq]
    refine ⟨lt_of_le_of_ne hyIco.1 ?_, hyIco.2⟩
    intro h0
    apply hxp
    simp only [mem_singleton_iff]
    rw [hxy, ← h0, hp]
  refine ⟨θ, hval, ?_⟩
  -- continuity via sequential continuity of the restriction
  set D : Set X := CZ \ {p} with hDdef
  rw [continuousOn_iff_continuous_restrict]
  have hseq : SeqContinuous (D.restrict θ) := by
    intro U x₀ hU
    -- `u n = (U n : X)`, values in `D`
    set u : ℕ → X := fun n => (U n : X) with hudef
    set xs : X := (x₀ : X) with hxsdef
    have hu : Filter.Tendsto u Filter.atTop (𝓝 xs) :=
      (continuous_subtype_val.tendsto x₀).comp hU
    have humem : ∀ n, u n ∈ D := fun n => (U n).2
    have hxsmem : xs ∈ D := x₀.2
    -- sequences of parameters
    set s : ℕ → ℝ := fun n => θ (u n) with hsdef
    set ss : ℝ := θ xs with hssdef
    have hs_mem : ∀ n, s n ∈ Set.Icc (0 : ℝ) 1 := fun n =>
      ⟨le_of_lt (hval (u n) (humem n)).2.1, le_of_lt (hval (u n) (humem n)).2.2⟩
    -- goal: `Tendsto s atTop (𝓝 ss)`
    have hgoal : Filter.Tendsto s Filter.atTop (𝓝 ss) := by
      refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
      obtain ⟨a, ha_mem, φ, hφmono, hφ⟩ :=
        (isCompact_Icc (a := (0 : ℝ)) (b := 1)).tendsto_subseq
          (x := fun n => s (ns n)) (fun n => hs_mem (ns n))
      -- `γ (s m) = u m`
      have hγs : ∀ m, γ (s m) = u m := fun m => (hval (u m) (humem m)).1
      -- `γ a = xs`
      have hns_tendsto : Filter.Tendsto (fun k => ns (φ k)) Filter.atTop Filter.atTop :=
        hns.comp hφmono.tendsto_atTop
      have hu_sub : Filter.Tendsto (fun k => u (ns (φ k))) Filter.atTop (𝓝 xs) :=
        hu.comp hns_tendsto
      have hγsub : Filter.Tendsto (fun k => γ (s (ns (φ k)))) Filter.atTop (𝓝 (γ a)) :=
        (hγc.tendsto a).comp hφ
      have hγsub' : Filter.Tendsto (fun k => γ (s (ns (φ k)))) Filter.atTop (𝓝 xs) := by
        have : (fun k => γ (s (ns (φ k)))) = fun k => u (ns (φ k)) := by
          funext k; exact hγs (ns (φ k))
        rw [this]; exact hu_sub
      have hγa : γ a = xs := tendsto_nhds_unique hγsub hγsub'
      -- `a = ss`
      have haIco : a ∈ Set.Ico (0 : ℝ) 1 := by
        refine ⟨ha_mem.1, lt_of_le_of_ne ha_mem.2 ?_⟩
        intro h1
        rw [h1, hγ1] at hγa
        exact hxsmem.2 (mem_singleton_iff.mpr hγa.symm)
      have hssIco : ss ∈ Set.Ico (0 : ℝ) 1 :=
        ⟨le_of_lt (hval xs hxsmem).2.1, (hval xs hxsmem).2.2⟩
      have hγss : γ ss = xs := (hval xs hxsmem).1
      have haeq : a = ss := hγi haIco hssIco (by rw [hγa, hγss])
      exact ⟨φ, by rw [← haeq]; exact hφ⟩
    exact hgoal
  exact hseq.continuous
/-! ## The ray-collar datum -/

/-- **Corner-matched ray-collar datum for one complement end.**  Packages the
point-set input the Tietze collapse consumes for an end `Z` with frontier circle
`CZ`, parametrisation `γ` and base point `p = γ 0`.

Intended model (built by part A from chart rectangles along a polyline ray): two
*half-collars* `Sm, Sp` — closed images of `[0,∞) × [0,1]` glued along a common ray
edge `R` — with collar coordinate data `dm, dp` that vanish / saturate along the ray
(`dm = 0`, `dp = 1` on `R`) and, at the circle edge, match the angular coordinate
exactly (`γ (dm x) = x` on `Sm ∩ CZ`, so `dm ≈ ε·s` there; `γ (dp x) = x` on
`Sp ∩ CZ`, so `dp ≈ 1 - ε·s`).  This *corner matching* is what lets the side data
meet the circle data continuously near `p`, curing the unsatisfiability of a naive
"two open sides" datum (whose closures cannot avoid `CZ ∖ {p}` while covering the
`Z`-side near `p`).

Together with the "big arc" `γ '' Icc ε (1-ε)` (carried by the angular coordinate
`θ`), the collars cover the whole circle (`hCZcover`); they cover a neighbourhood of
the ray (`hcov`) and of the `Z`-side near `p` (`hcovp`).  Only continuity and
value / closure properties are demanded, so part A is free to realise `dm, dp` as
any continuous data with these edges (e.g. `ε·s·χ(t)` and `1 - ε·s·χ(t)` in collar
coordinates, `χ(0) = 1`, `χ ≡ 0` for `t ≥ 1`). -/
structure RayCollar (X : Type*) [TopologicalSpace X] (Z CZ : Set X) (γ : ℝ → X)
    (p : X) where
  /-- The shared ray edge of the two half-collars, closed in `X`. -/
  R : Set X
  /-- The minus (`θ ≈ 0`) half-collar image, closed in `X`. -/
  Sm : Set X
  /-- The plus (`θ ≈ 1`) half-collar image, closed in `X`. -/
  Sp : Set X
  /-- Collar coordinate on `Sm`: `0` on the ray, `≈ θ` on the circle edge. -/
  dm : X → ℝ
  /-- Collar coordinate on `Sp`: `1` on the ray, `≈ θ` on the circle edge. -/
  dp : X → ℝ
  /-- Half-width of the two circle arcs cut out by the collars. -/
  ε : ℝ
  hε : 0 < ε
  hε1 : ε < 1
  hRcl : IsClosed R
  hSmcl : IsClosed Sm
  hSpcl : IsClosed Sp
  hpR : p ∈ R
  hRSm : R ⊆ Sm
  hRSp : R ⊆ Sp
  hRZ : R \ {p} ⊆ Z
  hSmZ : Sm ⊆ Z ∪ CZ
  hSpZ : Sp ⊆ Z ∪ CZ
  hSmSp : Sm ∩ Sp ⊆ R
  hdm_cont : ContinuousOn dm Sm
  hdp_cont : ContinuousOn dp Sp
  hdm_range : ∀ x ∈ Sm, dm x ∈ Set.Icc (0 : ℝ) 1
  hdp_range : ∀ x ∈ Sp, dp x ∈ Set.Icc (0 : ℝ) 1
  hdm_R : ∀ x ∈ R, dm x = 0
  hdp_R : ∀ x ∈ R, dp x = 1
  hdm_CZ : ∀ x ∈ Sm ∩ CZ, γ (dm x) = x
  hdp_CZ : ∀ x ∈ Sp ∩ CZ, γ (dp x) = x
  hCZcover : CZ ⊆ Sm ∪ Sp ∪ γ '' Set.Icc ε (1 - ε)
  hcov : ∀ r ∈ R \ {p}, ∀ᶠ x in 𝓝 r, x ∈ Sm ∪ Sp
  hcovp : ∀ᶠ x in 𝓝 p, x ∈ Z → x ∈ Sm ∪ Sp

/-! ## The collapse map from a ray-collar datum -/

/-- **Per-end collapse from a ray-collar datum.**  Given the frontier
parametrisation `γ` and a `RayCollar` for the end `Z`, produce the continuous
collapse `h : C(X, X)` fixing everything outside `Z` and mapping `Z` into
`closure V`.

The angular data `d` (`θ` on the big arc, `dm` on `Sm`, `dp` on `Sp`) is continuous
on the closed subset `Bs` of the punctured collar `Y = (Z ∪ CZ) ∖ R`; Tietze-extend
to `M`, set `Ψ = γ ∘ M` on `Y` and `Ψ = p` on `R`.  Corner matching (`dm = θ` on
`Sm ∩ CZ` by injectivity of `γ`, `dm = 0` / `dp = 1` on `R`) makes `Ψ` continuous
across the ray (periodicity `γ 1 = γ 0 = p` heals the angular jump) and equal to the
identity on `CZ`; `Ψ` glues with the identity outside `Z` into `h`. -/
theorem collapse_of_rayCollar {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [LocallyCompactSpace X]
    {V Z CZ : Set X} {γ : ℝ → X} {p : X}
    (hZo : IsOpen Z) (hCZ : CZ = frontier Z) (hCV : CZ ⊆ closure V)
    (hγc : Continuous γ) (hγp : Function.Periodic γ 1)
    (hγr : Set.range γ = CZ) (hγi : Set.InjOn γ (Set.Ico (0 : ℝ) 1)) (hp : γ 0 = p)
    (rc : RayCollar X Z CZ γ p) :
    ∃ h : C(X, X), (∀ y ∉ Z, h y = y) ∧ (∀ y ∈ Z, h y ∈ closure V) := by
  classical
  obtain ⟨R, Sm, Sp, dm, dp, ε, hε, hε1, hRcl, hSmcl, hSpcl, hpR, hRSm, hRSp, hRZ,
    hSmZ, hSpZ, hSmSp, hdm_cont, hdp_cont, hdm_range, hdp_range, hdm_R, hdp_R,
    hdm_CZ, hdp_CZ, hCZcover, hcov, hcovp⟩ := rc
  haveI : MetrizableSpace X := inferInstance
  have hγ1 : γ 1 = p := by have h := hγp 0; rw [zero_add] at h; rw [h, hp]
  -- frontier facts
  have hCZcl : IsClosed CZ := by rw [hCZ]; exact isClosed_frontier
  have hCZZ : ∀ x ∈ CZ, x ∉ Z := by
    intro x hx
    rw [hCZ] at hx
    have : x ∉ interior Z := hx.2
    rwa [hZo.interior_eq] at this
  set cZ : Set X := Z ∪ CZ with hcZdef
  have hclZ : closure Z = cZ := by
    rw [hcZdef, hCZ]
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inl hxZ
      · refine Or.inr ⟨hx, ?_⟩
        rw [hZo.interior_eq]; exact hxZ
    · rintro x (hxZ | hxf)
      · exact subset_closure hxZ
      · exact hxf.1
  have hcZcl : IsClosed cZ := hclZ ▸ isClosed_closure
  have hpCZ : p ∈ CZ := by rw [← hγr, ← hp]; exact mem_range_self 0
  have hRCZ : ∀ x ∈ R, x ∈ CZ → x = p := by
    intro x hxR hxCZ
    by_contra hxp
    exact hCZZ x hxCZ (hRZ ⟨hxR, by simpa using hxp⟩)
  -- angular coordinate
  obtain ⟨θ, hθval, hθcont⟩ := exists_angle hγc hγp hγr hγi hp
  -- big-arc facts
  have hBigArc_sub : γ '' Set.Icc ε (1 - ε) ⊆ CZ \ {p} := by
    rintro _ ⟨s, hs, rfl⟩
    have hsIco : s ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨le_trans hε.le hs.1, lt_of_le_of_lt hs.2 (by linarith [hε])⟩
    refine ⟨by rw [← hγr]; exact mem_range_self s, ?_⟩
    simp only [mem_singleton_iff]
    intro h
    have h0 : γ s = γ 0 := by rw [h, hp]
    have hs0 : s = 0 := hγi hsIco (by norm_num) h0
    linarith [hε, hs.1]
  have hBigArc_closed : IsClosed (γ '' Set.Icc ε (1 - ε)) :=
    (isCompact_Icc.image hγc).isClosed
  have hp_notArc : p ∉ γ '' Set.Icc ε (1 - ε) := fun hpa => (hBigArc_sub hpa).2 rfl
  -- the punctured-collar subspace `Y`
  set Y : Set X := cZ \ R with hYdef
  have hSmY : ∀ x ∈ Sm, x ∉ R → x ∈ Y := fun x hx hxR => ⟨hSmZ hx, hxR⟩
  have hSpY : ∀ x ∈ Sp, x ∉ R → x ∈ Y := fun x hx hxR => ⟨hSpZ hx, hxR⟩
  have hCZY : ∀ x ∈ CZ \ {p}, x ∈ Y := by
    rintro x ⟨hxCZ, hxp⟩
    refine ⟨Or.inr hxCZ, ?_⟩
    intro hxR
    exact hxp (mem_singleton_iff.mpr (hRCZ x hxR hxCZ))
  have hArcY : ∀ x ∈ γ '' Set.Icc ε (1 - ε), x ∈ Y := fun x hx => hCZY x (hBigArc_sub hx)
  haveI : NormalSpace ↥Y := inferInstance
  -- corner-matching of the collar coordinates with the angular coordinate
  have hmatch_m : ∀ x ∈ Sm, x ∈ CZ → x ≠ p → dm x = θ x := by
    intro x hxSm hxCZ hxp
    have hγdm : γ (dm x) = x := hdm_CZ x ⟨hxSm, hxCZ⟩
    have hdmr : dm x ∈ Set.Icc (0 : ℝ) 1 := hdm_range x hxSm
    have hne1 : dm x ≠ 1 := by
      intro h1; apply hxp; rw [← hγdm, h1, hγ1]
    have hdmIco : dm x ∈ Set.Ico (0 : ℝ) 1 := ⟨hdmr.1, lt_of_le_of_ne hdmr.2 hne1⟩
    have hθv := hθval x ⟨hxCZ, by simpa using hxp⟩
    have hθIco : θ x ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt hθv.2.1, hθv.2.2⟩
    exact hγi hdmIco hθIco (by rw [hγdm, hθv.1])
  have hmatch_p : ∀ x ∈ Sp, x ∈ CZ → x ≠ p → dp x = θ x := by
    intro x hxSp hxCZ hxp
    have hγdp : γ (dp x) = x := hdp_CZ x ⟨hxSp, hxCZ⟩
    have hdpr : dp x ∈ Set.Icc (0 : ℝ) 1 := hdp_range x hxSp
    have hne1 : dp x ≠ 1 := by
      intro h1; apply hxp; rw [← hγdp, h1, hγ1]
    have hdpIco : dp x ∈ Set.Ico (0 : ℝ) 1 := ⟨hdpr.1, lt_of_le_of_ne hdpr.2 hne1⟩
    have hθv := hθval x ⟨hxCZ, by simpa using hxp⟩
    have hθIco : θ x ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt hθv.2.1, hθv.2.2⟩
    exact hγi hdpIco hθIco (by rw [hγdp, hθv.1])
  -- the angular data on `↥Y`
  set d : ↥Y → ℝ := fun y =>
    if (y : X) ∈ Sm then dm (y : X) else if (y : X) ∈ Sp then dp (y : X) else θ (y : X)
    with hddef
  have hd_Sm : ∀ y : ↥Y, (y : X) ∈ Sm → d y = dm (y : X) := by
    intro y hy; simp only [hddef]; rw [if_pos hy]
  have hd_Sp : ∀ y : ↥Y, (y : X) ∈ Sp → (y : X) ∉ Sm → d y = dp (y : X) := by
    intro y hy hnm; simp only [hddef]; rw [if_neg hnm, if_pos hy]
  have hd_arc : ∀ y : ↥Y, (y : X) ∈ γ '' Set.Icc ε (1 - ε) → d y = θ (y : X) := by
    intro y hy
    have hyCZ : (y : X) ∈ CZ \ {p} := hBigArc_sub hy
    have hyne : (y : X) ≠ p := by simpa using hyCZ.2
    by_cases hySm : (y : X) ∈ Sm
    · simp only [hddef]; rw [if_pos hySm]; exact hmatch_m (y : X) hySm hyCZ.1 hyne
    · by_cases hySp : (y : X) ∈ Sp
      · simp only [hddef]; rw [if_neg hySm, if_pos hySp]; exact hmatch_p (y : X) hySp hyCZ.1 hyne
      · simp only [hddef]; rw [if_neg hySm, if_neg hySp]
  -- closed data set `Bs`
  set P_Sm : Set ↥Y := Subtype.val ⁻¹' Sm with hP_Smdef
  set P_Sp : Set ↥Y := Subtype.val ⁻¹' Sp with hP_Spdef
  set P_arc : Set ↥Y := Subtype.val ⁻¹' (γ '' Set.Icc ε (1 - ε)) with hP_arcdef
  have hP_Smcl : IsClosed P_Sm := hSmcl.preimage continuous_subtype_val
  have hP_Spcl : IsClosed P_Sp := hSpcl.preimage continuous_subtype_val
  have hP_arccl : IsClosed P_arc := hBigArc_closed.preimage continuous_subtype_val
  set Bs : Set ↥Y := (P_Sm ∪ P_Sp) ∪ P_arc with hBsdef
  have hBscl : IsClosed Bs := (hP_Smcl.union hP_Spcl).union hP_arccl
  -- continuity of `d` on `Bs`
  have hd_cont : ContinuousOn d Bs := by
    have hcSm : ContinuousOn d P_Sm := by
      have hcomp : ContinuousOn (fun y : ↥Y => dm (y : X)) P_Sm :=
        hdm_cont.comp continuous_subtype_val.continuousOn (fun y hy => hy)
      exact hcomp.congr (fun y hy => hd_Sm y hy)
    have hcSp : ContinuousOn d P_Sp := by
      have hcomp : ContinuousOn (fun y : ↥Y => dp (y : X)) P_Sp :=
        hdp_cont.comp continuous_subtype_val.continuousOn (fun y hy => hy)
      exact hcomp.congr (fun y hy => hd_Sp y hy (fun h => y.2.2 (hSmSp ⟨h, hy⟩)))
    have hcArc : ContinuousOn d P_arc := by
      have hcomp : ContinuousOn (fun y : ↥Y => θ (y : X)) P_arc :=
        hθcont.comp continuous_subtype_val.continuousOn (fun y hy => hBigArc_sub hy)
      exact hcomp.congr (fun y hy => hd_arc y hy)
    exact (hcSm.union_of_isClosed hcSp hP_Smcl hP_Spcl).union_of_isClosed hcArc
      (hP_Smcl.union hP_Spcl) hP_arccl
  -- Tietze extension
  obtain ⟨g, hg⟩ :=
    (⟨Bs.restrict d, continuousOn_iff_continuous_restrict.mp hd_cont⟩ : C(↥Bs, ℝ)).exists_restrict_eq
      hBscl
  have hgd : ∀ y : ↥Y, y ∈ Bs → g y = d y := by
    intro y hy
    have := DFunLike.congr_fun hg ⟨y, hy⟩
    simpa using this
  -- extend to a total real map `M`
  set M : X → ℝ := fun x => if h : x ∈ Y then g ⟨x, h⟩ else 0 with hMdef
  have hM_cont : ContinuousOn M Y := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Y.restrict M = fun y : ↥Y => g y := by
      funext y
      show M (y : X) = g y
      simp only [hMdef, dif_pos y.2, Subtype.coe_eta]
    rw [heq]; exact map_continuous g
  have hM_Sm : ∀ x ∈ Sm, x ∉ R → M x = dm x := by
    intro x hx hxR
    have hxY := hSmY x hx hxR
    have hxBs : (⟨x, hxY⟩ : ↥Y) ∈ Bs := Or.inl (Or.inl hx)
    have : g ⟨x, hxY⟩ = dm x := by rw [hgd ⟨x, hxY⟩ hxBs]; exact hd_Sm ⟨x, hxY⟩ hx
    simp only [hMdef, dif_pos hxY]; exact this
  have hM_Sp : ∀ x ∈ Sp, x ∉ R → M x = dp x := by
    intro x hx hxR
    have hxY := hSpY x hx hxR
    have hxnm : x ∉ Sm := fun h => hxR (hSmSp ⟨h, hx⟩)
    have hxBs : (⟨x, hxY⟩ : ↥Y) ∈ Bs := Or.inl (Or.inr hx)
    have : g ⟨x, hxY⟩ = dp x := by
      rw [hgd ⟨x, hxY⟩ hxBs]; exact hd_Sp ⟨x, hxY⟩ hx hxnm
    simp only [hMdef, dif_pos hxY]; exact this
  have hM_arc : ∀ x ∈ γ '' Set.Icc ε (1 - ε), M x = θ x := by
    intro x hx
    have hxY := hArcY x hx
    have hxBs : (⟨x, hxY⟩ : ↥Y) ∈ Bs := Or.inr hx
    have : g ⟨x, hxY⟩ = θ x := by rw [hgd ⟨x, hxY⟩ hxBs]; exact hd_arc ⟨x, hxY⟩ hx
    simp only [hMdef, dif_pos hxY]; exact this
  -- the collapse of the closed collar
  set Ψ : X → X := fun x => if x ∈ R then p else γ (M x) with hΨdef
  have hΨCZ : ∀ x, Ψ x ∈ CZ := by
    intro x
    by_cases hxR : x ∈ R
    · simp only [hΨdef, if_pos hxR]; exact hpCZ
    · simp only [hΨdef, if_neg hxR, ← hγr]; exact mem_range_self _
  have hΨid : ∀ x ∈ CZ, Ψ x = x := by
    intro x hx
    by_cases hxp : x = p
    · subst hxp; simp only [hΨdef, if_pos hpR]
    · have hxR : x ∉ R := fun h => hxp (hRCZ x h hx)
      simp only [hΨdef, if_neg hxR]
      rcases hCZcover hx with hu | hBig
      · rcases hu with hxSm | hxSp
        · rw [hM_Sm x hxSm hxR]; exact hdm_CZ x ⟨hxSm, hx⟩
        · rw [hM_Sp x hxSp hxR]; exact hdp_CZ x ⟨hxSp, hx⟩
      · rw [hM_arc x hBig]; exact (hθval x ⟨hx, by simpa using hxp⟩).1
  have hΨY : Set.EqOn Ψ (fun x => γ (M x)) Y := fun y hy => by
    simp only [hΨdef, if_neg hy.2]
  -- neighbourhood coverage of the ray by the two collars (inside `cZ`)
  have hcovR : ∀ r ∈ R, ∀ᶠ x in 𝓝[cZ] r, x ∈ Sm ∪ Sp := by
    intro r hrR
    by_cases hrp : r = p
    · subst hrp
      have h1 : ∀ᶠ x in 𝓝[cZ] r, x ∈ Z → x ∈ Sm ∪ Sp :=
        hcovp.filter_mono nhdsWithin_le_nhds
      have h2 : ∀ᶠ x in 𝓝[cZ] r, x ∈ cZ := self_mem_nhdsWithin
      have h3 : ∀ᶠ x in 𝓝[cZ] r, x ∈ (γ '' Set.Icc ε (1 - ε))ᶜ :=
        nhdsWithin_le_nhds (hBigArc_closed.isOpen_compl.mem_nhds hp_notArc)
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      rcases hx2 with hxZ | hxCZ
      · exact hx1 hxZ
      · rcases hCZcover hxCZ with hu | hBig
        · exact hu
        · exact absurd hBig hx3
    · exact (hcov r ⟨hrR, by simpa using hrp⟩).filter_mono nhdsWithin_le_nhds
  -- continuity of `Ψ` at every ray point (value `p`)
  have hΨR : ∀ r ∈ R, ContinuousWithinAt Ψ cZ r := by
    intro r hrR
    have hΨr : Ψ r = p := by simp only [hΨdef, if_pos hrR]
    have hrSm : r ∈ Sm := hRSm hrR
    have hrSp : r ∈ Sp := hRSp hrR
    have htend : Filter.Tendsto Ψ (𝓝[cZ] r) (𝓝 p) := by
      rw [Filter.tendsto_def]; intro N hN
      have hpN : p ∈ N := mem_of_mem_nhds hN
      have hcmval : γ (dm r) = p := by rw [hdm_R r hrR, hp]
      have hcpval : γ (dp r) = p := by rw [hdp_R r hrR, hγ1]
      have hcm : ContinuousWithinAt (fun x => γ (dm x)) Sm r :=
        (hγc.comp_continuousOn hdm_cont).continuousWithinAt hrSm
      have hcp : ContinuousWithinAt (fun x => γ (dp x)) Sp r :=
        (hγc.comp_continuousOn hdp_cont).continuousWithinAt hrSp
      have hm : ∀ᶠ x in 𝓝 r, x ∈ Sm → γ (dm x) ∈ N := by
        rw [← eventually_nhdsWithin_iff]
        exact hcm.tendsto.eventually_mem (by rw [hcmval]; exact hN)
      have hp' : ∀ᶠ x in 𝓝 r, x ∈ Sp → γ (dp x) ∈ N := by
        rw [← eventually_nhdsWithin_iff]
        exact hcp.tendsto.eventually_mem (by rw [hcpval]; exact hN)
      filter_upwards [hcovR r hrR, hm.filter_mono nhdsWithin_le_nhds,
        hp'.filter_mono nhdsWithin_le_nhds] with x hxcov hxm hxp
      show Ψ x ∈ N
      by_cases hxR : x ∈ R
      · rw [show Ψ x = p from by simp only [hΨdef, if_pos hxR]]; exact hpN
      · rcases hxcov with hxSm | hxSp
        · rw [show Ψ x = γ (dm x) from by
              simp only [hΨdef, if_neg hxR]; rw [hM_Sm x hxSm hxR]]
          exact hxm hxSm
        · rw [show Ψ x = γ (dp x) from by
              simp only [hΨdef, if_neg hxR]; rw [hM_Sp x hxSp hxR]]
          exact hxp hxSp
    rw [ContinuousWithinAt, hΨr]; exact htend
  -- continuity of `Ψ` on `cZ`
  have hΨcont : ContinuousOn Ψ cZ := by
    intro x hx
    by_cases hxR : x ∈ R
    · exact hΨR x hxR
    · have hxY : x ∈ Y := ⟨hx, hxR⟩
      have hΨonY : ContinuousOn Ψ Y := (hγc.comp_continuousOn hM_cont).congr hΨY
      have hRc : Rᶜ ∈ 𝓝 x := hRcl.isOpen_compl.mem_nhds hxR
      have hstep : ContinuousWithinAt Ψ (cZ ∩ Rᶜ) x := by
        have heqY : cZ ∩ Rᶜ = Y := by rw [hYdef, Set.sdiff_eq]
        rw [heqY]; exact hΨonY x hxY
      exact (continuousWithinAt_inter hRc).mp hstep
  -- the collapse map `h`
  set h : X → X := fun x => if x ∈ Z then Ψ x else x with hhdef
  have hh_cZ : ContinuousOn h cZ := by
    refine hΨcont.congr (fun x hx => ?_)
    rcases hx with hxZ | hxCZ
    · simp only [hhdef, if_pos hxZ]
    · have hxnZ : x ∉ Z := hCZZ x hxCZ
      simp only [hhdef, if_neg hxnZ]
      exact (hΨid x hxCZ).symm
  have hh_out : ContinuousOn h (Zᶜ) := by
    refine (continuousOn_id).congr (fun x hx => ?_)
    simp only [hhdef, if_neg hx, id_eq]
  have hh_cont : Continuous h := by
    have hcov_univ : (Set.univ : Set X) = cZ ∪ Zᶜ := by
      apply Set.Subset.antisymm
      · intro x _
        by_cases hxZ : x ∈ Z
        · exact Or.inl (Or.inl hxZ)
        · exact Or.inr hxZ
      · exact fun _ _ => trivial
    have hZccl : IsClosed (Zᶜ) := hZo.isClosed_compl
    have : ContinuousOn h Set.univ := by
      rw [hcov_univ]
      exact hh_cZ.union_of_isClosed hh_out hcZcl hZccl
    exact continuousOn_univ.mp this
  refine ⟨⟨h, hh_cont⟩, ?_, ?_⟩
  · intro y hy
    simp only [ContinuousMap.coe_mk, hhdef, if_neg hy]
  · intro y hy
    simp only [ContinuousMap.coe_mk, hhdef, if_pos hy]
    exact hCV (hΨCZ y)

/-! ## Reduction of the per-end collapse to a supply of ray-collar data -/

section Reduction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The per-end collapse reduces to a ray-collar supply.**  Under the standard
per-end hypotheses of `exists_end_collapse`, if for the end
`Z = connectedComponentIn (closure V)ᶜ x` *every* periodic parametrisation `γ` of
its frontier circle admits a `RayCollar`, then the per-end collapse exists.

The frontier `frontier Z` is a single connected component of `frontier V` (it is
preconnected — the crossing-parity capstone — and a union of whole components), so
`exists_periodic_param` supplies the parametrisation; `collapse_of_rayCollar` then
turns the ray-collar datum into the collapse.  Discharging the sole remaining sorry
`exists_end_collapse` thus reduces to proving `hA` (part A: the geometric
construction of the cutting ray with a two-sided collar). -/
theorem exists_end_collapse_of_rayCollar [T2Space X] [ConnectedSpace X]
    [SimplyConnectedSpace X] {V : Set X} (hVo : IsOpen V) (hVconn : IsConnected V)
    (hVcl : IsCompact (closure V)) {f : X → ℝ} {c : ℝ} {A : Set X} (hAo : IsOpen A)
    (hfrA : frontier V ⊆ A) (hharm : SurfaceHarmonicOn f A)
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    {x : X} (hx : x ∈ (closure V)ᶜ)
    (hA : ∀ γ : ℝ → X, Continuous γ → Function.Periodic γ 1 →
        Set.range γ = frontier (connectedComponentIn (closure V)ᶜ x) →
        Set.InjOn γ (Set.Ico (0 : ℝ) 1) →
        Nonempty (RayCollar X (connectedComponentIn (closure V)ᶜ x)
          (frontier (connectedComponentIn (closure V)ᶜ x)) γ (γ 0))) :
    ∃ h : C(X, X),
      (∀ y ∉ connectedComponentIn (closure V)ᶜ x, h y = y) ∧
      (∀ y ∈ connectedComponentIn (closure V)ᶜ x, h y ∈ closure V) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  haveI : SecondCountableTopology X := Rado.secondCountableTopology_of_riemannSurface
  haveI : LocallyCompactSpace X := Rado.locallyCompactSpace
  set Z := connectedComponentIn (closure V)ᶜ x with hZdef
  have hZo : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  obtain ⟨ξ₀, hξ₀⟩ := nonempty_frontier_component_compl_closure hVconn.nonempty hx
  have hξ₀frV : ξ₀ ∈ frontier V := frontier_component_compl_closure_subset hξ₀
  have hfrZpre : IsPreconnected (frontier Z) :=
    isPreconnected_frontier_component_compl_closure hVo hVcl hVconn hdich hfc hchart hx
  have hCZeq : frontier Z = connectedComponentIn (frontier V) ξ₀ := by
    apply Set.Subset.antisymm
    · exact hfrZpre.subset_connectedComponentIn hξ₀
        (frontier_component_compl_closure_subset)
    · exact frontier_component_compl_closure_component_subset hVo hdich hfc hchart hξ₀
  obtain ⟨γ, hγc, hγp, hγr, hγi⟩ :=
    exists_periodic_param hVo hVcl hdich hfc hchart hharm hAo hfrA hξ₀frV
  have hγrZ : Set.range γ = frontier Z := by rw [hγr, ← hCZeq]
  obtain ⟨rc⟩ := hA γ hγc hγp hγrZ hγi
  have hCV : frontier Z ⊆ closure V :=
    (frontier_component_compl_closure_subset).trans frontier_subset_closure
  exact collapse_of_rayCollar hZo rfl hCV hγc hγp hγrZ hγi rfl rc

end Reduction

end Uniformization
