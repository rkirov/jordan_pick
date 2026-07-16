/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Rado.Surface.Germs

/-!
# Removable singularity for bounded harmonic functions (Anghel–Stan Lemma 8)

A harmonic function on a punctured disk that is bounded near the puncture
extends harmonically across the puncture.

Proof route (planar, Poisson + barrier maximum principle; no complex analysis).
Fix a radius `r = R/2`.  Let `v` be the Poisson extension of `u|_{sphere c r}`
into `ball c r`; it is harmonic on `ball c r`, continuous on `closedBall c r`,
equals `u` on `sphere c r`, and is bounded by the same `M`.  The difference
`u - v` is harmonic on the punctured disk, bounded, and vanishes on `sphere c r`.
Comparison with the harmonic barrier `ε·(log r − log‖z − c‖)` on annuli
`ρ < ‖z − c‖ < r` (Rado's `SubMeanOn.le_of_frontier_le`) forces `u - v = 0`
on the punctured disk after letting `ρ → 0` and `ε → 0`.  Hence
`v` (extended by the single value `v c` at `c`) is the harmonic extension.
-/

open Set Metric InnerProductSpace

namespace Uniformization

/-- **Barrier lemma.** If `d` is harmonic on the punctured disk `ball c r \ {c}`,
continuous up to `closedBall c r \ {c}`, bounded above by `N` there, and vanishes
on `sphere c r`, then `d ≤ 0` on the whole punctured disk. -/
private lemma barrier_le_zero {c : ℂ} {r N : ℝ} (hr : 0 < r) {d : ℂ → ℝ}
    (hd_harm : HarmonicOnNhd d (ball c r \ {c}))
    (hd_cont : ContinuousOn d (closedBall c r \ {c}))
    (hd_bd : ∀ z ∈ closedBall c r \ {c}, d z ≤ N)
    (hd_sphere : ∀ z ∈ sphere c r, d z = 0) :
    ∀ z ∈ ball c r \ {c}, d z ≤ 0 := by
  intro z₀ hz₀
  set d₀ : ℝ := dist z₀ c with hd₀def
  have hz₀ne : z₀ ≠ c := fun h => hz₀.2 (mem_singleton_iff.mpr h)
  have hd₀pos : 0 < d₀ := dist_pos.mpr hz₀ne
  have hd₀r : d₀ < r := mem_ball.mp hz₀.1
  have hz₀norm : ‖z₀ - c‖ = d₀ := (dist_eq_norm z₀ c).symm
  -- The one-sided barrier bound `d z₀ ≤ ε·(log r − log d₀)` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → d z₀ ≤ ε * (Real.log r - Real.log d₀) := by
    intro ε hε
    have hεne : ε ≠ 0 := hε.ne'
    -- choose the inner radius `ρ` small enough that the barrier dominates `N`.
    set ρ : ℝ := min (d₀ / 2) (Real.exp (Real.log r - N / ε)) with hρdef
    have hexppos : (0:ℝ) < Real.exp (Real.log r - N / ε) := Real.exp_pos _
    have hρpos : 0 < ρ := lt_min (half_pos hd₀pos) hexppos
    have hρd₀ : ρ < d₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hd₀pos)
    have hρr : ρ < r := hρd₀.trans hd₀r
    have hρbnd : N ≤ ε * (Real.log r - Real.log ρ) := by
      have h1 : ρ ≤ Real.exp (Real.log r - N / ε) := min_le_right _ _
      have h2 : Real.log ρ ≤ Real.log r - N / ε := by
        have := (Real.log_le_log_iff hρpos hexppos).mpr h1
        rwa [Real.log_exp] at this
      have h3 : N / ε ≤ Real.log r - Real.log ρ := by linarith
      calc N = ε * (N / ε) := by field_simp
        _ ≤ ε * (Real.log r - Real.log ρ) := mul_le_mul_of_nonneg_left h3 hε.le
    -- the open annulus
    set A : Set ℂ := ball c r ∩ (closedBall c ρ)ᶜ with hAdef
    have hAopen : IsOpen A := isOpen_ball.inter (isOpen_compl_iff.mpr isClosed_closedBall)
    have hAbdd : Bornology.IsBounded A := isBounded_ball.subset (fun z hz => hz.1)
    have hA_sub_P : A ⊆ ball c r \ {c} := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      rw [mem_singleton_iff]
      intro h; subst h
      exact hz.2 (mem_closedBall_self hρpos.le)
    have hĀ_sub_P : closedBall c r ∩ (ball c ρ)ᶜ ⊆ closedBall c r \ {c} := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      rw [mem_singleton_iff]
      intro h; subst h
      exact hz.2 (mem_ball_self hρpos)
    -- harmonicity of the barrier `log‖z − c‖` on the annulus
    have hβharm : HarmonicOnNhd (fun z => Real.log ‖z - c‖) A := by
      intro z hz
      have hzc : z ≠ c := (hA_sub_P hz).2
      have haf : AnalyticAt ℂ (fun w => w - c) z := analyticAt_id.sub analyticAt_const
      exact haf.harmonicAt_log_norm (sub_ne_zero.mpr hzc)
    have hβfull_h : HarmonicOnNhd (fun z => Real.log r - Real.log ‖z - c‖) A :=
      (harmonicOnNhd_const (Real.log r)).sub hβharm
    have hdharm : HarmonicOnNhd d A := hd_harm.mono hA_sub_P
    -- the comparison function `G = d − ε·(log r − log‖z − c‖)`
    set G : ℂ → ℝ := d - ε • (fun z => Real.log r - Real.log ‖z - c‖) with hGdef
    have hGval : ∀ x, G x = d x - ε * (Real.log r - Real.log ‖x - c‖) := by
      intro x
      rw [hGdef]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hGharm : HarmonicOnNhd G A := hdharm.sub hβfull_h.const_smul
    have hGsub : Rado.SubMeanOn G A := (Rado.HarmonicOnNhd.meanEqOn hGharm).subMeanOn
    -- continuity of `G` up to the closed annulus
    have hβfull_cont : ContinuousOn (fun z => Real.log r - Real.log ‖z - c‖)
        (closedBall c r ∩ (ball c ρ)ᶜ) := by
      apply ContinuousOn.sub continuousOn_const
      apply Real.continuousOn_log.comp
        ((continuous_id.sub continuous_const).norm).continuousOn
      intro z hz
      simp only [mem_compl_iff, mem_singleton_iff]
      have hzne : z ≠ c := by
        intro h; subst h; exact hz.2 (mem_ball_self hρpos)
      simpa [norm_eq_zero, sub_eq_zero] using hzne
    have hGcont_Ā : ContinuousOn G (closedBall c r ∩ (ball c ρ)ᶜ) := by
      rw [hGdef]
      exact (hd_cont.mono hĀ_sub_P).sub (hβfull_cont.const_smul ε)
    have hclA : closure A ⊆ closedBall c r ∩ (ball c ρ)ᶜ := by
      apply closure_minimal
      · intro z hz
        exact ⟨ball_subset_closedBall hz.1, fun hb => hz.2 (ball_subset_closedBall hb)⟩
      · exact isClosed_closedBall.inter (isClosed_compl_iff.mpr isOpen_ball)
    have hGcont : ContinuousOn G (closure A) := hGcont_Ā.mono hclA
    -- boundary values on the frontier of the annulus
    have hbd : ∀ x ∈ frontier A, G x ≤ 0 := by
      intro x hx
      rw [hAdef] at hx
      have hxsub : x ∈ sphere c r ∪ sphere c ρ := by
        have h := frontier_inter_subset (ball c r) ((closedBall c ρ)ᶜ) hx
        rw [frontier_ball c hr.ne', frontier_compl, frontier_closedBall c hρpos.ne'] at h
        rcases h with h | h
        · exact Or.inl h.1
        · exact Or.inr h.2
      rcases hxsub with hxr | hxρ
      · have hdx : dist x c = r := mem_sphere.mp hxr
        have hxnorm : ‖x - c‖ = r := by rw [← dist_eq_norm]; exact hdx
        rw [hGval x, hxnorm, sub_self, mul_zero, sub_zero]
        exact le_of_eq (hd_sphere x hxr)
      · have hdx : dist x c = ρ := mem_sphere.mp hxρ
        have hxnorm : ‖x - c‖ = ρ := by rw [← dist_eq_norm]; exact hdx
        have hxP : x ∈ closedBall c r \ {c} := by
          refine ⟨mem_closedBall.mpr ?_, ?_⟩
          · rw [hdx]; exact hρr.le
          · rw [mem_singleton_iff]
            intro h; subst h
            rw [dist_self] at hdx
            exact absurd hdx (ne_of_lt hρpos)
        rw [hGval x, hxnorm]
        linarith [hd_bd x hxP, hρbnd]
    -- maximum principle on the annulus
    have hfinal := hGsub.le_of_frontier_le hAopen hAbdd hGcont hbd
    have hz₀A : z₀ ∈ A := by
      refine ⟨hz₀.1, ?_⟩
      intro h
      exact absurd (mem_closedBall.mp h) (not_le.mpr hρd₀)
    have hGz₀ := hfinal z₀ (subset_closure hz₀A)
    rw [hGval z₀, hz₀norm] at hGz₀
    linarith
  -- let `ε → 0`
  by_contra hcon
  rw [not_le] at hcon
  set C : ℝ := Real.log r - Real.log d₀ with hCdef
  have hCpos : 0 < C := by
    have := Real.log_lt_log hd₀pos hd₀r
    rw [hCdef]; linarith
  have hCne : C ≠ 0 := hCpos.ne'
  have hεc : (0:ℝ) < d z₀ / (2 * C) := div_pos hcon (by positivity)
  have hk := key (d z₀ / (2 * C)) hεc
  have hsimp : d z₀ / (2 * C) * C = d z₀ / 2 := by field_simp
  rw [hsimp] at hk
  linarith

/-- **Removable singularity for bounded harmonic functions** (Anghel–Stan Lemma 8).
A harmonic function on a punctured ball, bounded near the puncture, extends
harmonically across the puncture. -/
theorem exists_harmonicOnNhd_extension_of_bounded {c : ℂ} {R : ℝ} (hR : 0 < R)
    {u : ℂ → ℝ} {M : ℝ} (hu : HarmonicOnNhd u (ball c R \ {c}))
    (hbd : ∀ z ∈ ball c R \ {c}, |u z| ≤ M) :
    ∃ v : ℂ → ℝ, HarmonicOnNhd v (ball c R) ∧ EqOn v u (ball c R \ {c}) := by
  set r : ℝ := R / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  have hrR : r < R := by rw [hr_def]; linarith
  -- boundary data
  have hsphere_sub : sphere c r ⊆ ball c R \ {c} := by
    intro z hz
    rw [mem_sphere] at hz
    refine ⟨mem_ball.mpr ?_, ?_⟩
    · rw [hz]; exact hrR
    · rw [mem_singleton_iff]
      intro h; subst h
      rw [dist_self] at hz
      exact absurd hz (ne_of_lt hr)
  have hf : ContinuousOn u (sphere c r) := hu.continuousOn.mono hsphere_sub
  set v : ℂ → ℝ := Rado.poissonExtension u c r with hv_def
  have hv_harm : HarmonicOnNhd v (ball c r) := Rado.poissonExtension_harmonicOnNhd hr hf
  have hv_cont : ContinuousOn v (closedBall c r) := Rado.poissonExtension_continuousOn hr hf
  have hv_sphere : EqOn v u (sphere c r) := Rado.poissonExtension_eqOn_sphere hr hf
  have hv_Icc : ∀ z ∈ closedBall c r, v z ∈ Icc (-M) M := by
    apply Rado.poissonExtension_mem_Icc hr hf
    intro z hz
    rw [mem_Icc]
    have h := hbd z (hsphere_sub hz)
    rw [abs_le] at h
    exact ⟨h.1, h.2⟩
  -- shared harmonicity / continuity facts on the small disk
  have hu_P : HarmonicOnNhd u (ball c r \ {c}) :=
    hu.mono (fun z hz => ⟨ball_subset_ball hrR.le hz.1, hz.2⟩)
  have hv_P : HarmonicOnNhd v (ball c r \ {c}) := hv_harm.mono Set.sdiff_subset
  have hu_cont_cb : ContinuousOn u (closedBall c r \ {c}) :=
    hu.continuousOn.mono (fun z hz => ⟨closedBall_subset_ball hrR hz.1, hz.2⟩)
  have hv_cont_cb : ContinuousOn v (closedBall c r \ {c}) := hv_cont.mono Set.sdiff_subset
  -- `u ≤ v` on the punctured disk (barrier applied to `u − v`)
  have hle1 : ∀ z ∈ ball c r \ {c}, u z - v z ≤ 0 := by
    refine barrier_le_zero (N := 2 * M) hr (hu_P.sub hv_P) (hu_cont_cb.sub hv_cont_cb) ?_ ?_
    · intro z hz
      have hu_z : |u z| ≤ M := hbd z ⟨closedBall_subset_ball hrR hz.1, hz.2⟩
      have hv_z := hv_Icc z hz.1
      rw [abs_le] at hu_z
      rw [mem_Icc] at hv_z
      show u z - v z ≤ 2 * M
      linarith [hu_z.1, hu_z.2, hv_z.1, hv_z.2]
    · intro z hz
      show u z - v z = 0
      rw [hv_sphere hz]; ring
  -- `v ≤ u` on the punctured disk (barrier applied to `v − u`)
  have hle2 : ∀ z ∈ ball c r \ {c}, v z - u z ≤ 0 := by
    refine barrier_le_zero (N := 2 * M) hr (hv_P.sub hu_P) (hv_cont_cb.sub hu_cont_cb) ?_ ?_
    · intro z hz
      have hu_z : |u z| ≤ M := hbd z ⟨closedBall_subset_ball hrR hz.1, hz.2⟩
      have hv_z := hv_Icc z hz.1
      rw [abs_le] at hu_z
      rw [mem_Icc] at hv_z
      show v z - u z ≤ 2 * M
      linarith [hu_z.1, hu_z.2, hv_z.1, hv_z.2]
    · intro z hz
      show v z - u z = 0
      rw [hv_sphere hz]; ring
  have huv : EqOn u v (ball c r \ {c}) := fun z hz =>
    le_antisymm (by have := hle1 z hz; linarith) (by have := hle2 z hz; linarith)
  -- the extension: `u` off `c`, patched with `v c` at `c`
  set V : ℂ → ℝ := fun z => if z = c then v c else u z with hV_def
  have hV_eqOn : EqOn V u (ball c R \ {c}) := by
    intro z hz
    rw [hV_def]
    simp only [if_neg (fun h => hz.2 (mem_singleton_iff.mpr h))]
  have hV_harm : HarmonicOnNhd V (ball c R) := by
    intro z hz
    by_cases hzc : z = c
    · have hz_mem : z ∈ ball c r := by rw [hzc]; exact mem_ball_self hr
      have hev : V =ᶠ[nhds z] v := by
        filter_upwards [isOpen_ball.mem_nhds hz_mem] with y hy
        by_cases hyc : y = c
        · simp [hV_def, hyc]
        · rw [hV_def]
          simp only [if_neg hyc]
          exact huv ⟨hy, fun h => hyc (mem_singleton_iff.mp h)⟩
      exact (harmonicAt_congr_nhds hev).2 (hv_harm z hz_mem)
    · have hmem : z ∈ ball c R \ {c} := ⟨hz, fun h => hzc (mem_singleton_iff.mp h)⟩
      have hev : V =ᶠ[nhds z] u := by
        filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hmem] with y hy
        rw [hV_def]
        simp only [if_neg (fun h => hy.2 (mem_singleton_iff.mpr h))]
      exact (harmonicAt_congr_nhds hev).2 (hu z hmem)
  exact ⟨V, hV_harm, hV_eqOn⟩

end Uniformization
