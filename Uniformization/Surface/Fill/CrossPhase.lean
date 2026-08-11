/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.EndParity
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The crossing phase of a frontier component (W7 step L5.4b)

For a single connected component `C = connectedComponentIn (frontier V) x₀` of the
level set `frontier V`, this file packages the **crossing phase** `τ : C(X, Circle)`
that winds once (`0 ↦ 2π`) across `C` inside a collar `N` and is trivial (`= 1`)
outside it.  This is the surface-topology object consumed by the winding-parity
contradiction: a loop crossing two distinct components of `frontier V` lifts to a
path whose endpoints differ, contradicting `SimplyConnectedSpace X`.

## The ramp profile

The winding is driven by the piecewise-linear `ramp t = min 1 (max 0 (t + 1/2))`,
which is `0` for `t ≤ -1/2`, climbs linearly to `1` on `[-1/2, 1/2]`, and stays
`1` for `t ≥ 1/2`.  Feeding the normalised collar coordinate `(f x − c)/δ` into
`Circle.exp (2π · ramp ·)` gives a phase that is `1` (`= exp 0 = exp 2π`) on both
sides of the collar and turns once through the middle.

## The construction

The point-set substrate is `exists_component_collar_substrate` (`EndParity`): it
supplies a phantom-free neighbourhood `M ⊇ frontier V` with `f` continuous there,
a collar `N` with compact closure `⊆ M`, `closure N ∩ frontier V = C`, and
`f ≠ c` on `frontier N`.  Compactness of `frontier N` turns the pointwise
non-vanishing into a *uniform* margin `δ`, and the phase is pasted from the
`ramp` formula on `N` and the constant `1` on `X ∖ K'`, where
`K' = {x ∈ closure N | |f x − c| ≤ δ}` is a compact subset of `N`.  The two pieces
agree (both give `1`) on their overlap because `ramp` saturates once `|f − c| > δ`.

The main output is `exists_crossingPhase`, packaged in the structure
`CrossingPhase`.  The consumer-facing saturation lemma `CrossingPhase.τ_eq_one_of_side`
and the elementary `ramp` lemmas are exported for the winding argument.
-/

open Set Metric Topology Filter

namespace Uniformization

/-! ## The ramp profile -/

/-- The piecewise-linear ramp `min 1 (max 0 (t + 1/2))`: value `0` for `t ≤ -1/2`,
linear on `[-1/2, 1/2]`, value `1` for `t ≥ 1/2`. -/
noncomputable def ramp (t : ℝ) : ℝ := min 1 (max 0 (t + 1 / 2))

/-- `ramp` saturates at `0` on the far-negative side. -/
theorem ramp_of_le {t : ℝ} (h : t ≤ -(1 / 2)) : ramp t = 0 := by
  unfold ramp
  rw [max_eq_left (by linarith : t + 1 / 2 ≤ 0), min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

/-- `ramp` saturates at `1` on the far-positive side. -/
theorem ramp_of_ge {t : ℝ} (h : 1 / 2 ≤ t) : ramp t = 1 := by
  unfold ramp
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ t + 1 / 2), min_eq_left (by linarith : (1 : ℝ) ≤ t + 1 / 2)]

/-- `ramp` is continuous. -/
theorem ramp_continuous : Continuous ramp := by
  unfold ramp; fun_prop

/-- `ramp` is monotone. -/
theorem ramp_monotone : Monotone ramp := by
  intro a b hab
  unfold ramp
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

/-! ## The crossing-phase structure -/

section Structure

variable {X : Type*} [TopologicalSpace X]

/-- **The crossing phase of a frontier component.**  For a level coordinate `f`
with level value `c` and a component `C ⊆ frontier V`, this bundles a global phase
`τ : C(X, Circle)` supported on a collar `N` of `C` together with the point-set
data (`M, N, δ`) certifying that `τ` winds once across `C` and is trivial away
from it. -/
structure CrossingPhase (V : Set X) (f : X → ℝ) (c : ℝ) (C : Set X) where
  /-- The crossing phase, a global continuous map to the circle. -/
  τ : C(X, Circle)
  /-- The collar neighbourhood of the component `C`. -/
  N : Set X
  /-- The phantom-free neighbourhood of `frontier V` on which `f` is continuous. -/
  M : Set X
  /-- The half-width of the ramp in the collar coordinate. -/
  δ : ℝ
  δ_pos : 0 < δ
  N_open : IsOpen N
  M_open : IsOpen M
  C_sub_N : C ⊆ N
  N_sub_M : closure N ⊆ M
  f_cont : ContinuousOn f M
  level_iff : ∀ x ∈ M, (f x = c ↔ x ∈ frontier V)
  pos_iff : ∀ x ∈ M, (c < f x ↔ x ∈ V)
  closureN_frontier : closure N ∩ frontier V = C
  τ_off : ∀ x ∉ N, τ x = 1
  τ_on : ∀ x ∈ N, τ x = Circle.exp (2 * Real.pi * ramp ((f x - c) / δ))
  gap : ∀ x ∈ frontier N, δ * 2 ≤ |f x - c|

/-- **Saturation of the crossing phase.**  Inside the collar `N`, once the collar
coordinate `f` is on either far side of the level value (`f x ≤ c − δ` or
`c + δ ≤ f x`), the phase is trivial.  This is the fact the winding argument uses
to see `τ` as a *local* crossing supported near `C`. -/
theorem CrossingPhase.τ_eq_one_of_side {V : Set X} {f : X → ℝ} {c : ℝ} {C : Set X}
    (P : CrossingPhase V f c C) {x : X} (hx : x ∈ P.N)
    (h : f x ≤ c - P.δ ∨ c + P.δ ≤ f x) : P.τ x = 1 := by
  rw [P.τ_on x hx]
  rcases h with h | h
  · have hle : (f x - c) / P.δ ≤ -(1 / 2) := by
      rw [div_le_iff₀ P.δ_pos]; linarith [P.δ_pos]
    rw [ramp_of_le hle, mul_zero, Circle.exp_zero]
  · have hge : (1 : ℝ) / 2 ≤ (f x - c) / P.δ := by
      rw [le_div_iff₀ P.δ_pos]; linarith [P.δ_pos]
    rw [ramp_of_ge hge, mul_one, Circle.exp_two_pi]

end Structure

/-! ## Existence of the crossing phase -/

section Surface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

open Rado

/-- **Per-frontier-point box with the sign law.**  As `exists_box_nbhd`
(`EndParity`), but additionally exporting the *positivity* characterisation
`c < f x ↔ x ∈ V` on the box (the `{re > c}` half is `V`). -/
theorem exists_box_nbhd_pos [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {ξ : X} (hξ : ξ ∈ frontier V) :
    ∃ W : Set X, IsOpen W ∧ ξ ∈ W ∧ ContinuousOn f W ∧
      (∀ x ∈ W, (f x = c ↔ x ∈ frontier V)) ∧
      (∀ x ∈ W, (c < f x ↔ x ∈ V)) := by
  obtain ⟨ψ, δ, ε, hψ, hξψ, hδ, hε, hqre, hbox_tgt, hWopen, hξW, hf_eq, hVeq, hfront⟩ :=
    exists_straight_box hVo hdich hfc hchart hξ
  set box := straightBox (ψ ξ) c δ ε with hboxdef
  set W := ψ.symm '' box with hWdef
  have hWsrc : W ⊆ ψ.source := by
    rintro x ⟨z, hz, rfl⟩; exact ψ.map_target (hbox_tgt hz)
  refine ⟨W, hWopen, hξW, ?_, ?_, ?_⟩
  · exact (Complex.continuous_re.comp_continuousOn (ψ.continuousOn.mono hWsrc)).congr
      (fun x hx => (re_eq_f_of_mem_boxImage hbox_tgt hf_eq hx).symm)
  · -- level law
    intro x hxW
    constructor
    · intro hfx
      obtain ⟨z, hz, rfl⟩ := hxW
      have hzre : z.re = c := by rw [← hf_eq z hz]; exact hfx
      have : ψ.symm z ∈ frontier V ∩ W := by
        rw [hfront]; exact ⟨z, ⟨hz, hzre⟩, rfl⟩
      exact this.1
    · exact fun hxfr => hfc x hxfr
  · -- sign law
    intro x hxW
    constructor
    · intro hlt
      obtain ⟨z, hz, rfl⟩ := hxW
      have hzre : c < z.re := by rw [← hf_eq z hz]; exact hlt
      have : ψ.symm z ∈ V ∩ W := by rw [hVeq]; exact ⟨z, ⟨hz, hzre⟩, rfl⟩
      exact this.1
    · intro hxV
      have hmem : x ∈ V ∩ W := ⟨hxV, hxW⟩
      rw [hVeq] at hmem
      obtain ⟨z', ⟨hz', hz'lt⟩, rfl⟩ := hmem
      rw [hf_eq z' hz']; exact hz'lt

/-- **Phantom-free collar neighbourhood with the sign law.**  As
`exists_phantom_free_nbhd`, but the neighbourhood `M` additionally satisfies the
positivity law `c < f x ↔ x ∈ V`. -/
theorem exists_phantom_free_pos_nbhd [T2Space X] {V : Set X} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0) :
    ∃ M : Set X, IsOpen M ∧ frontier V ⊆ M ∧ ContinuousOn f M ∧
      (∀ x ∈ M, (f x = c ↔ x ∈ frontier V)) ∧
      (∀ x ∈ M, (c < f x ↔ x ∈ V)) := by
  classical
  have hfrcpt : IsCompact (frontier V) :=
    hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  choose! Wf hWopen hWmem hWcont hWphantom hWpos using
    fun ξ (hξ : ξ ∈ frontier V) => exists_box_nbhd_pos hVo hdich hfc hchart hξ
  obtain ⟨t, htsub, htfin, htcov⟩ := hfrcpt.elim_finite_subcover_image hWopen
    (fun ξ hξ => Set.mem_biUnion hξ (hWmem ξ hξ))
  refine ⟨⋃ ξ ∈ t, Wf ξ, isOpen_biUnion (fun ξ hξ => hWopen ξ (htsub hξ)), htcov, ?_, ?_, ?_⟩
  · intro x hxM
    obtain ⟨ξ, hξt, hxW⟩ := mem_iUnion₂.mp hxM
    exact ((hWcont ξ (htsub hξt)).continuousAt
      ((hWopen ξ (htsub hξt)).mem_nhds hxW)).continuousWithinAt
  · intro x hxM
    obtain ⟨ξ, hξt, hxW⟩ := mem_iUnion₂.mp hxM
    exact hWphantom ξ (htsub hξt) x hxW
  · intro x hxM
    obtain ⟨ξ, hξt, hxW⟩ := mem_iUnion₂.mp hxM
    exact hWpos ξ (htsub hξt) x hxW

/-- **Collar substrate with the sign law.**  As `exists_component_collar_substrate`
(`EndParity`), but on the phantom-free neighbourhood `M` the sign law
`c < f x ↔ x ∈ V` holds as well. -/
theorem exists_component_collar_substrate_pos [T2Space X] {V : Set X} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x₀ : X} :
    ∃ (M N : Set X), IsOpen M ∧ IsOpen N ∧ ContinuousOn f M ∧
      (∀ x ∈ M, (f x = c ↔ x ∈ frontier V)) ∧
      (∀ x ∈ M, (c < f x ↔ x ∈ V)) ∧
      connectedComponentIn (frontier V) x₀ ⊆ N ∧
      IsCompact (closure N) ∧ closure N ⊆ M ∧
      closure N ∩ frontier V = connectedComponentIn (frontier V) x₀ ∧
      (∀ x ∈ frontier N, f x ≠ c) := by
  have : LocallyCompactSpace X := Rado.locallyCompactSpace
  set C := connectedComponentIn (frontier V) x₀ with hCeq
  obtain ⟨M, hMopen, hfrM, hfcont, hphantom, hpos⟩ :=
    exists_phantom_free_pos_nbhd hVo hVcl hdich hfc hchart
  have hfrcpt : IsCompact (frontier V) :=
    hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hCcl : IsClosed C := isClosed_frontier.connectedComponentIn
  have hCsub : C ⊆ frontier V := connectedComponentIn_subset _ _
  obtain ⟨U, hUo, hCU⟩ := isOpen_component_in_frontier hVo hdich hfc hchart (x₀ := x₀)
  obtain ⟨N, hNo, hCN, hNcpt, hNM, hNfr⟩ :=
    exists_open_isCompact_closure_inter_eq hfrcpt hCcl hCsub hUo hCU hMopen (hCsub.trans hfrM)
  refine ⟨M, N, hMopen, hNo, hfcont, hphantom, hpos, hCN, hNcpt, hNM, hNfr, ?_⟩
  intro x hxfrN hfx
  rw [hNo.frontier_eq] at hxfrN
  have hxfr : x ∈ frontier V := (hphantom x (hNM hxfrN.1)).mp hfx
  have hxC : x ∈ C := hNfr ▸ ⟨hxfrN.1, hxfr⟩
  exact hxfrN.2 (hCN hxC)

/-- **Existence of the crossing phase for a frontier component.**  Under the piece
hypotheses of `Push.exists_push_into`, every frontier point `x₀` gives rise to a
`CrossingPhase` for its component `connectedComponentIn (frontier V) x₀`. -/
theorem exists_crossingPhase [T2Space X] {V : Set X} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x₀ : X} :
    Nonempty (CrossingPhase V f c (connectedComponentIn (frontier V) x₀)) := by
  classical
  obtain ⟨M, N, hMopen, hNopen, hfcont, hphantom, hpos, hCN, hNcpt, hNM, hNfrEq, hNfr⟩ :=
    exists_component_collar_substrate_pos hVo hVcl hdich hfc hchart (x₀ := x₀)
  -- uniform margin `δ` on `frontier N`
  have hfrNcpt : IsCompact (frontier N) :=
    hNcpt.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfrNsubM : frontier N ⊆ M := frontier_subset_closure.trans hNM
  have hcontfr : ContinuousOn (fun x => |f x - c|) (frontier N) :=
    ((hfcont.mono hfrNsubM).sub continuousOn_const).abs
  obtain ⟨δ₀, hδ₀pos, hδ₀le⟩ := hfrNcpt.exists_forall_le' hcontfr (a := 0)
    (fun b hb => abs_pos.mpr (sub_ne_zero.mpr (hNfr b hb)))
  set δ : ℝ := δ₀ / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hgap : ∀ x ∈ frontier N, δ * 2 ≤ |f x - c| := by
    intro x hx
    have := hδ₀le x hx
    rw [hδdef]; linarith
  -- the compact core `K'` inside `N`
  set K' : Set X := closure N ∩ (fun x => |f x - c|) ⁻¹' (Set.Iic δ) with hK'def
  have hK'closed : IsClosed K' := by
    rw [hK'def]
    exact ((hfcont.mono hNM).sub continuousOn_const).abs.preimage_isClosed_of_isClosed
      isClosed_closure isClosed_Iic
  have hK'sub : K' ⊆ N := by
    intro x hx
    have hxcl : x ∈ closure N := hx.1
    have hxle : |f x - c| ≤ δ := hx.2
    by_contra hxN
    have hxfr : x ∈ frontier N := by rw [hNopen.frontier_eq]; exact ⟨hxcl, hxN⟩
    have := hgap x hxfr
    linarith
  -- the phase, pasted from the ramp formula on `N` and `1` off `K'`
  set τfun : X → Circle :=
    fun x => if x ∈ N then Circle.exp (2 * Real.pi * ramp ((f x - c) / δ)) else 1 with hτdef
  have hτ_on : ∀ x ∈ N, τfun x = Circle.exp (2 * Real.pi * ramp ((f x - c) / δ)) :=
    fun x hx => if_pos hx
  have hτ_off : ∀ x ∉ N, τfun x = 1 := fun x hx => if_neg hx
  -- `ramp` saturation: once `|f − c| > δ`, the formula is `1`
  have hg_sat : ∀ y : X, δ < |f y - c| →
      Circle.exp (2 * Real.pi * ramp ((f y - c) / δ)) = 1 := by
    intro y hy
    rcases lt_or_ge (f y - c) 0 with hz | hz
    · rw [abs_of_neg hz] at hy
      have ht : (f y - c) / δ ≤ -(1 / 2) := by rw [div_le_iff₀ hδ]; linarith
      rw [ramp_of_le ht, mul_zero, Circle.exp_zero]
    · rw [abs_of_nonneg hz] at hy
      have ht : (1 : ℝ) / 2 ≤ (f y - c) / δ := by rw [le_div_iff₀ hδ]; linarith
      rw [ramp_of_ge ht, mul_one, Circle.exp_two_pi]
  -- the phase is `1` off `K'`
  have hτone_off : ∀ y : X, y ∉ K' → τfun y = 1 := by
    intro y hy
    by_cases hyN : y ∈ N
    · rw [hτ_on y hyN]
      apply hg_sat
      have hycl : y ∈ closure N := subset_closure hyN
      by_contra hle
      exact hy ⟨hycl, not_lt.mp hle⟩
    · exact hτ_off y hyN
  -- global continuity of the phase
  have hcont : Continuous τfun := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ N
    · have hxM : x ∈ M := hNM (subset_closure hx)
      have hfx : ContinuousAt f x := hfcont.continuousAt (hMopen.mem_nhds hxM)
      have hform : ContinuousAt
          (fun y => Circle.exp (2 * Real.pi * ramp ((f y - c) / δ))) x := by
        have h1 : ContinuousAt (fun y => (f y - c) / δ) x :=
          (hfx.sub continuousAt_const).div_const δ
        have h2 : ContinuousAt (fun y => 2 * Real.pi * ramp ((f y - c) / δ)) x :=
          continuousAt_const.mul (ramp_continuous.continuousAt.comp h1)
        exact Circle.exp.continuous.continuousAt.comp h2
      refine hform.congr ?_
      filter_upwards [hNopen.mem_nhds hx] with y hy
      exact (if_pos hy).symm
    · have hxK' : x ∉ K' := fun h => hx (hK'sub h)
      refine (continuousAt_const : ContinuousAt (fun _ : X => (1 : Circle)) x).congr ?_
      filter_upwards [hK'closed.isOpen_compl.mem_nhds hxK'] with y hy
      exact (hτone_off y hy).symm
  -- package
  exact ⟨{
    τ := ⟨τfun, hcont⟩
    N := N
    M := M
    δ := δ
    δ_pos := hδ
    N_open := hNopen
    M_open := hMopen
    C_sub_N := hCN
    N_sub_M := hNM
    f_cont := hfcont
    level_iff := hphantom
    pos_iff := hpos
    closureN_frontier := hNfrEq
    τ_off := fun x hx => hτ_off x hx
    τ_on := fun x hx => hτ_on x hx
    gap := hgap }⟩

end Surface

end Uniformization
