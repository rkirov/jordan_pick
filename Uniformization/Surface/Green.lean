/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Regularity
import Uniformization.Complex.RemovableHarmonic

/-!
# Green's function with logarithmic pole (Anghel–Stan Proposition 9)

On a relatively compact, connected, exterior-disk-regular open `U ⊆ X` with
`x₀ ∈ U`, there is a Green's function: continuous on `closure U \ {x₀}`,
harmonic on `U \ {x₀}`, zero on `frontier U`, positive inside, with
`G ∘ e.symm + log‖·‖` extending harmonically across `0` in a chart `e`
centered at `x₀`.

Proof plan (A–S Prop 9): fix a chart disk `D` at `x₀`; solve the Dirichlet
problem (`exists_dirichlet_solution`) on `U \ e.symm '' closedBall 0 (1/2)`
with data `1` on the inner circle, `0` on `frontier U`, giving `h₁`; choose
`A B` with `B·a < A < B·(1 − …)` as in the paper and form the subharmonic
comparison function `h = max (−B·h₁) (log‖·‖ − A)`; run Perron on the family
of nonneg subharmonic `g` vanishing on the frontier with `g + h ≤ 0`
(renormalized into `[0,1]` to fit `Rado.IsPerronFamily`); the sup `G` is
harmonic on `U \ {x₀}`, sandwiched `−log‖ξ‖ ≤ G ≤ A − log‖ξ‖` near `x₀`, so
`G + log‖ξ‖` is bounded and `exists_harmonicOnNhd_extension_of_bounded`
finishes the pole normalization. Positivity via the strong minimum principle
(`Rado.SubMeanOn.eqOn_const_of_isMaxOn` applied to `−G`).
-/

open Set Metric Topology MeasureTheory InnerProductSpace Complex Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Generic helpers -/

section

set_option linter.unusedSectionVars false

/-! ## Locally bounded Perron families

Adaptation of Radó's Perron-envelope harmonicity theorem (`Rado.Surface.Perron`)
from the hardwired `Icc 0 1` bound to a *locally bounded* family, needed for a
Green's function whose members have a `-log` pole and are unbounded near the
pole. -/

structure LocBoundedPerronFamily (𝓕 : Set (X → ℝ)) (s : Set X) : Prop where
  nonempty : 𝓕.Nonempty
  subharmonic : ∀ g ∈ 𝓕, SurfaceSubharmonicOn g s
  nonneg : ∀ g ∈ 𝓕, ∀ x ∈ s, 0 ≤ g x
  locBdd : ∀ x ∈ s, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ M : ℝ, ∀ g ∈ 𝓕, ∀ y ∈ V ∩ s, g y ≤ M
  max_mem : ∀ g₁ ∈ 𝓕, ∀ g₂ ∈ 𝓕, (fun x ↦ Max.max (g₁ x) (g₂ x)) ∈ 𝓕
  replace_mem : ∀ g ∈ 𝓕, ∀ e c r, IsReplaceDisk e c r s → surfaceReplace g e c r ∈ 𝓕

/-! ### Harnack's principle (copied verbatim from `Rado.Surface.Perron`) -/

/-- The Poisson kernel is continuous on the boundary circle, for a fixed
interior point. -/
private theorem continuousOn_poissonKernel_sphere' {z₀ w : ℂ} {R : ℝ}
    (hw : w ∈ ball z₀ R) : ContinuousOn (poissonKernel z₀ w) (sphere z₀ R) := by
  have hdR : ‖w - z₀‖ < R := mem_ball_iff_norm.mp hw
  have hfun : poissonKernel z₀ w
      = fun z ↦ (‖z - z₀‖ ^ 2 - ‖w - z₀‖ ^ 2) / ‖(z - z₀) - (w - z₀)‖ ^ 2 :=
    funext fun z ↦ poissonKernel_def z₀ w z
  intro z hz
  have hzR : ‖z - z₀‖ = R := mem_sphere_iff_norm.mp hz
  have hne : (z - z₀) - (w - z₀) ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    rw [hcon] at hzR
    exact hdR.ne hzR
  apply ContinuousAt.continuousWithinAt
  rw [hfun]
  exact ContinuousAt.div (by fun_prop) (by fun_prop)
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

/-- **Harnack's inequality**, upper bound. -/
private theorem harnack_le' {h : ℂ → ℝ} {z₀ w : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : HarmonicOnNhd h (closedBall z₀ R))
    (hpos : ∀ z ∈ closedBall z₀ R, 0 ≤ h z) (hw : w ∈ ball z₀ R) :
    h w ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := by
  have hcont : ContinuousOn h (sphere z₀ R) := fun z hz ↦
    ((hh z (sphere_subset_closedBall hz)).1.continuousAt).continuousWithinAt
  have hker : ContinuousOn (poissonKernel z₀ w) (sphere z₀ R) :=
    continuousOn_poissonKernel_sphere' hw
  have hrep : Real.circleAverage (poissonKernel z₀ w • h) z₀ R = h w :=
    hh.circleAverage_poissonKernel_smul hw
  have hmv : Real.circleAverage h z₀ R = h z₀ := by
    apply HarmonicOnNhd.circleAverage_eq
    rwa [abs_of_pos hR]
  have hint1 : CircleIntegrable (poissonKernel z₀ w • h) z₀ R :=
    (hker.smul hcont).circleIntegrable hR.le
  have hint2 : CircleIntegrable
      (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R :=
    (continuousOn_const.mul hcont).circleIntegrable hR.le
  have hmono : Real.circleAverage (poissonKernel z₀ w • h) z₀ R
      ≤ Real.circleAverage (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R := by
    refine Real.circleAverage_mono hint1 hint2 ?_
    intro z hz
    rw [abs_of_pos hR] at hz
    have hkb : poissonKernel z₀ w z ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) := by
      have h1 := re_herglotzRieszKernel_le hz hw
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      simpa [herglotzRieszKernel_def] using h1
    have h0 : 0 ≤ h z := hpos z (sphere_subset_closedBall hz)
    calc (poissonKernel z₀ w • h) z = poissonKernel z₀ w z * h z := rfl
      _ ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z := mul_le_mul_of_nonneg_right hkb h0
  have havg : Real.circleAverage (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R
      = (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := by
    have h1 : Real.circleAverage (fun z ↦ ((R + ‖w - z₀‖) / (R - ‖w - z₀‖)) • h z) z₀ R
        = ((R + ‖w - z₀‖) / (R - ‖w - z₀‖)) • Real.circleAverage h z₀ R :=
      Real.circleAverage_fun_smul
    simpa [smul_eq_mul, hmv] using h1
  calc h w = Real.circleAverage (poissonKernel z₀ w • h) z₀ R := hrep.symm
    _ ≤ Real.circleAverage (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R := hmono
    _ = (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := havg

/-- **Harnack's principle** (locally bounded case): the pointwise supremum of a
monotone sequence of `[0,M]`-valued harmonic functions on an open set is
harmonic. Generalizes the `Icc 0 1` version to a fixed real `M`. -/
private theorem harmonicOnNhd_ciSup_of_monotone' {h : ℕ → ℂ → ℝ} {U : Set ℂ} {M : ℝ}
    (hU : IsOpen U) (hharm : ∀ n, HarmonicOnNhd (h n) U)
    (hmono : ∀ z ∈ U, ∀ m n : ℕ, m ≤ n → h m z ≤ h n z)
    (hbd : ∀ n, ∀ z ∈ U, h n z ∈ Icc (0 : ℝ) M) :
    HarmonicOnNhd (fun z ↦ ⨆ n, h n z) U := by
  set W : ℂ → ℝ := fun z ↦ ⨆ n, h n z with hWdef
  have hWapp : ∀ z, W z = ⨆ n, h n z := fun z ↦ rfl
  have hbdd : ∀ z ∈ U, BddAbove (range fun n ↦ h n z) := fun z hz ↦
    ⟨M, by rintro v ⟨n, rfl⟩; exact (hbd n z hz).2⟩
  have hle : ∀ n, ∀ z ∈ U, h n z ≤ W z := fun n z hz ↦ le_ciSup (hbdd z hz) n
  have htend : ∀ z ∈ U, Tendsto (fun n ↦ h n z) atTop (𝓝 (W z)) := fun z hz ↦
    tendsto_atTop_ciSup (fun m n hmn ↦ hmono z hz m n hmn) (hbdd z hz)
  -- continuity of the supremum, via Harnack's inequality
  have hWc : ContinuousOn W U := by
    intro z₀ hz₀
    apply ContinuousAt.continuousWithinAt
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
    obtain ⟨m, hm⟩ : ∃ m, W z₀ - ε / 8 < h m z₀ := by
      have h1 : W z₀ - ε / 8 < ⨆ n, h n z₀ := by
        rw [← hWapp]; exact sub_lt_self _ (by linarith)
      exact exists_lt_of_lt_ciSup h1
    have hcm : ContinuousAt (h m) z₀ := (hharm m z₀ hz₀).1.continuousAt
    rw [Metric.continuousAt_iff] at hcm
    obtain ⟨δ₁, hδ₁, hδ₁p⟩ := hcm (ε / 8) (by linarith)
    -- Harnack control of the tail on the half ball
    have hkey : ∀ x ∈ ball z₀ (R / 2), W x - h m x ≤ 3 * (W z₀ - h m z₀) := by
      intro x hx
      have hxR : x ∈ ball z₀ R := ball_subset_ball (by linarith) hx
      have hxU : x ∈ U := hRU (ball_subset_closedBall hxR)
      have htends : Tendsto (fun n ↦ h n x - h m x) atTop (𝓝 (W x - h m x)) :=
        (htend x hxU).sub tendsto_const_nhds
      refine le_of_tendsto htends ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      have hdiff : HarmonicOnNhd (fun z ↦ h n z - h m z) (closedBall z₀ R) := fun z hz ↦
        (hharm n z (hRU hz)).sub (hharm m z (hRU hz))
      have hnonneg : ∀ z ∈ closedBall z₀ R, 0 ≤ h n z - h m z := fun z hz ↦
        sub_nonneg.mpr (hmono z (hRU hz) m n hn)
      have hHar := harnack_le' hR hdiff hnonneg hxR
      have hd2 : ‖x - z₀‖ < R / 2 := mem_ball_iff_norm.mp hx
      have hd0 : (0 : ℝ) ≤ ‖x - z₀‖ := norm_nonneg _
      have hfrac : (R + ‖x - z₀‖) / (R - ‖x - z₀‖) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have h0 : 0 ≤ h n z₀ - h m z₀ := sub_nonneg.mpr (hmono z₀ hz₀ m n hn)
      have hWn : h n z₀ ≤ W z₀ := hle n z₀ hz₀
      calc h n x - h m x ≤ (R + ‖x - z₀‖) / (R - ‖x - z₀‖) * (h n z₀ - h m z₀) := hHar
        _ ≤ 3 * (h n z₀ - h m z₀) := mul_le_mul_of_nonneg_right hfrac h0
        _ ≤ 3 * (W z₀ - h m z₀) := by linarith
    refine ⟨min δ₁ (R / 2), lt_min hδ₁ (by linarith), ?_⟩
    intro x hx
    have hx1 : dist x z₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : x ∈ ball z₀ (R / 2) := mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _))
    have hxU : x ∈ U := hRU (ball_subset_closedBall (ball_subset_ball (by linarith) hx2))
    have k1 := hkey x hx2
    have k2 : 0 ≤ W x - h m x := sub_nonneg.mpr (hle m x hxU)
    have k3 : |h m x - h m z₀| < ε / 8 := by
      have := hδ₁p hx1
      rwa [Real.dist_eq] at this
    have k4 : 0 ≤ W z₀ - h m z₀ := sub_nonneg.mpr (hle m z₀ hz₀)
    rw [Real.dist_eq, abs_lt]
    rw [abs_lt] at k3
    constructor
    · linarith [k3.1]
    · linarith [k3.2]
  -- the mean value property passes to the limit
  have hmean : MeanEqOn W U := by
    refine ⟨hWc, fun a ρ hρ hsub ↦ ?_⟩
    have haU : a ∈ U := hsub (mem_closedBall_self hρ.le)
    have hsph : sphere a ρ ⊆ U := sphere_subset_closedBall.trans hsub
    have hcm : ∀ n, Continuous fun θ : ℝ ↦ h n (circleMap a ρ θ) := by
      intro n
      refine continuous_iff_continuousAt.mpr fun θ ↦ ?_
      exact ((hharm n _ (hsph (circleMap_mem_sphere a hρ.le θ))).1.continuousAt).comp
        (continuous_circleMap a ρ).continuousAt
    have hci : Tendsto (fun n ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, h n (circleMap a ρ θ)) atTop
        (𝓝 (∫ θ in (0 : ℝ)..2 * Real.pi, W (circleMap a ρ θ))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ ↦ M) (Filter.Eventually.of_forall fun n ↦ (hcm n).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun n ↦ ae_of_all _ fun θ _ ↦ ?_)
        intervalIntegrable_const (ae_of_all _ fun θ _ ↦ ?_)
      · have hmem := hbd n _ (hsph (circleMap_mem_sphere a hρ.le θ))
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hmem.1, hmem.2], hmem.2⟩
      · exact htend _ (hsph (circleMap_mem_sphere a hρ.le θ))
    have h2 : Tendsto (fun n ↦ Real.circleAverage (h n) a ρ) atTop
        (𝓝 (Real.circleAverage W a ρ)) := by
      simp only [Real.circleAverage_def]
      exact hci.const_smul _
    have h3 : Tendsto (fun n ↦ Real.circleAverage (h n) a ρ) atTop (𝓝 (W a)) :=
      Filter.Tendsto.congr
        (fun n ↦ ((HarmonicOnNhd.meanEqOn (hharm n)).mean_eq a ρ hρ hsub).symm)
        (htend a haU)
    exact tendsto_nhds_unique h2 h3
  exact hmean.harmonicOnNhd hU

/-! ### The Perron approximation sequence (adapted to `LocBoundedPerronFamily`) -/

/-- Pointwise maximum of the first `j + 1` members of a sequence of functions. -/
private def maxUpTo' (f : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => f 0
  | j + 1 => fun y ↦ Max.max (maxUpTo' f j y) (f (j + 1) y)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem maxUpTo'_mem {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : LocBoundedPerronFamily 𝓕 s)
    {f : ℕ → X → ℝ} (hf : ∀ j, f j ∈ 𝓕) : ∀ j, maxUpTo' f j ∈ 𝓕 := by
  intro j
  induction j with
  | zero => rw [maxUpTo']; exact hf 0
  | succ j ih => rw [maxUpTo']; exact h𝓕.max_mem _ ih _ (hf (j + 1))

omit [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem le_maxUpTo' {f : ℕ → X → ℝ} {i j : ℕ} (hij : i ≤ j) (y : X) :
    f i y ≤ maxUpTo' f j y := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.mp hij
    rw [maxUpTo']
  | succ j ih =>
    rw [maxUpTo']
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_max_right _ _
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (le_max_left _ _)

/-- The recursive Perron approximation sequence. -/
private noncomputable def perronSeq' (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ)
    (b : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => surfaceReplace (b 0) e c r
  | n + 1 => surfaceReplace
      (fun y ↦ Max.max (perronSeq' e c r b n y) (b (n + 1) y)) e c r

section PerronSeq
variable {𝓕 : Set (X → ℝ)} {s : Set X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}
  {b : ℕ → X → ℝ}

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq'_mem (h𝓕 : LocBoundedPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s)
    (hb : ∀ n, b n ∈ 𝓕) : ∀ n, perronSeq' e c r b n ∈ 𝓕 := by
  intro n
  induction n with
  | zero =>
    rw [perronSeq']
    exact h𝓕.replace_mem _ (hb 0) e c r hd
  | succ n ih =>
    rw [perronSeq']
    exact h𝓕.replace_mem _ (h𝓕.max_mem _ ih _ (hb (n + 1))) e c r hd

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem le_perronSeq' (h𝓕 : LocBoundedPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    ∀ y ∈ s, b n y ≤ perronSeq' e c r b n y := by
  intro y hy
  cases n with
  | zero =>
    rw [perronSeq']
    exact le_surfaceReplace (h𝓕.subharmonic _ (hb 0)) hd y hy
  | succ n =>
    rw [perronSeq']
    refine le_trans (le_max_right (perronSeq' e c r b n y) (b (n + 1) y)) ?_
    exact le_surfaceReplace (h𝓕.subharmonic _
      (h𝓕.max_mem _ (perronSeq'_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd y hy

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq'_le_succ (h𝓕 : LocBoundedPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    ∀ y ∈ s, perronSeq' e c r b n y ≤ perronSeq' e c r b (n + 1) y := by
  intro y hy
  rw [perronSeq']
  refine le_trans (le_max_left (perronSeq' e c r b n y) (b (n + 1) y)) ?_
  exact le_surfaceReplace (h𝓕.subharmonic _
    (h𝓕.max_mem _ (perronSeq'_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd y hy

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq'_mono (h𝓕 : LocBoundedPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) {m n : ℕ} (hmn : m ≤ n) :
    ∀ y ∈ s, perronSeq' e c r b m y ≤ perronSeq' e c r b n y := by
  intro y hy
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact ih.trans (perronSeq'_le_succ h𝓕 hd hb n y hy)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq'_surfaceHarmonicOn (h𝓕 : LocBoundedPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    SurfaceHarmonicOn (perronSeq' e c r b n) (e.symm '' ball c r) := by
  cases n with
  | zero =>
    rw [perronSeq']
    exact surfaceReplace_surfaceHarmonicOn (h𝓕.subharmonic _ (hb 0)) hd
  | succ n =>
    rw [perronSeq']
    exact surfaceReplace_surfaceHarmonicOn (h𝓕.subharmonic _
      (h𝓕.max_mem _ (perronSeq'_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd

end PerronSeq

/-! ### The three theorems -/

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem LocBoundedPerronFamily.le_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : LocBoundedPerronFamily 𝓕 s) {g : X → ℝ} (hg : g ∈ 𝓕) :
    ∀ x ∈ s, g x ≤ perronSup 𝓕 x := by
  intro x hx
  obtain ⟨V, hVo, hxV, M, hMV⟩ := h𝓕.locBdd x hx
  exact le_csSup ⟨M, by rintro v ⟨g', hg', rfl⟩; exact hMV g' hg' x ⟨hxV, hx⟩⟩ ⟨g, hg, rfl⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem LocBoundedPerronFamily.perronSup_le {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : LocBoundedPerronFamily 𝓕 s) {M : ℝ} {x : X}
    (hM : ∀ g ∈ 𝓕, g x ≤ M) : perronSup 𝓕 x ≤ M :=
  csSup_le (h𝓕.nonempty.image _) fun _ ⟨g, hg, hgx⟩ ↦ hgx ▸ hM g hg

theorem LocBoundedPerronFamily.surfaceHarmonicOn_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    [T2Space X] (hs : IsOpen s) (h𝓕 : LocBoundedPerronFamily 𝓕 s) :
    SurfaceHarmonicOn (perronSup 𝓕) s := by
  refine SurfaceHarmonicOn.of_chartwise fun x hx ↦ ?_
  set e := chartAt ℂ x with he_def
  have he : e ∈ riemannAtlas X := chartAt_mem_riemannAtlas x
  have hxe : x ∈ e.source := mem_chart_source ℂ x
  refine ⟨e, he, hxe, ?_⟩
  -- local bound data around `x`
  obtain ⟨V, hVo, hxV, M, hMV⟩ := h𝓕.locBdd x hx
  set c : ℂ := e x with hc_def
  -- choose a legal replacement disk around `c = e x` inside `chartImage e s`
  -- AND whose preimage lies inside `V`
  have hmem : e x ∈ chartImage e s := mem_chartImage_of_mem hx hxe
  have hUopen : IsOpen (chartImage e s ∩ (e.target ∩ e.symm ⁻¹' V)) :=
    (isOpen_chartImage e hs).inter (e.symm.continuousOn.isOpen_inter_preimage e.open_target hVo)
  have hcU : c ∈ chartImage e s ∩ (e.target ∩ e.symm ⁻¹' V) := by
    refine ⟨hmem, e.map_source hxe, ?_⟩
    show e.symm (e x) ∈ V
    rw [e.left_inv hxe]; exact hxV
  obtain ⟨r, hr, hcb⟩ := nhds_basis_closedBall.mem_iff.mp (hUopen.mem_nhds hcU)
  have hcbCI : closedBall c r ⊆ chartImage e s := fun w hw ↦ (hcb hw).1
  have hcbV : closedBall c r ⊆ e.symm ⁻¹' V := fun w hw ↦ (hcb hw).2.2
  have hd : IsReplaceDisk e c r s :=
    ⟨he, hr, hcbCI.trans (chartImage_subset_target e s), by
      rintro y ⟨w, hw, rfl⟩
      exact mapsTo_symm_chartImage (hcbCI hw)⟩
  have hBmem : ∀ w ∈ ball c r, e.symm w ∈ s := fun w hw ↦
    hd.preimage_subset ⟨w, ball_subset_closedBall hw, rfl⟩
  -- the local bound, transported through the chart
  have hMbound : ∀ g ∈ 𝓕, ∀ w ∈ ball c r, g (e.symm w) ≤ M := fun g hg w hw ↦
    hMV g hg (e.symm w) ⟨hcbV (ball_subset_closedBall hw), hBmem w hw⟩
  have hball_sub : ball c r ⊆ chartImage e (e.symm '' ball c r) := by
    intro w hw
    have hwt : w ∈ e.target := hd.closedBall_subset (ball_subset_closedBall hw)
    exact ⟨e.symm w, ⟨⟨w, hw, rfl⟩, e.map_target hwt⟩, e.right_inv hwt⟩
  -- unfolded form of the envelope
  have hPS : ∀ y : X, perronSup 𝓕 y = sSup ((fun g ↦ g y) '' 𝓕) := fun y ↦ rfl
  -- boundedness of the family image, at chart-disk points (via the local bound)
  have hPSbddB : ∀ w ∈ ball c r, BddAbove ((fun g ↦ g (e.symm w)) '' 𝓕) := fun w hw ↦
    ⟨M, by rintro v ⟨g', hg', rfl⟩; exact hMbound g' hg' w hw⟩
  -- a dense sequence in the disk
  haveI hnB : Nonempty (ball c r) := ⟨⟨c, mem_ball_self hr⟩⟩
  set zs : ℕ → ℂ := fun j ↦ (TopologicalSpace.denseSeq (ball c r) j : ℂ) with hzs_def
  have hzs_mem : ∀ j, zs j ∈ ball c r := fun j ↦ (TopologicalSpace.denseSeq (ball c r) j).2
  have hzs_dense : ∀ w ∈ ball c r, w ∈ closure (range zs) := by
    intro w hw
    have h1 : (⟨w, hw⟩ : ball c r) ∈ closure (range (TopologicalSpace.denseSeq (ball c r))) :=
      TopologicalSpace.denseRange_denseSeq (ball c r) _
    have h2 : MapsTo (Subtype.val : ball c r → ℂ)
        (range (TopologicalSpace.denseSeq (ball c r))) (range zs) := by
      rintro q ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    exact map_mem_closure continuous_subtype_val h1 h2
  -- near-optimal family members at the dense points
  have hopt : ∀ j n : ℕ, ∃ g ∈ 𝓕,
      perronSup 𝓕 (e.symm (zs j)) - 1 / ((n : ℝ) + 1) < g (e.symm (zs j)) := by
    intro j n
    have h1 : perronSup 𝓕 (e.symm (zs j)) - 1 / ((n : ℝ) + 1)
        < sSup ((fun g ↦ g (e.symm (zs j))) '' 𝓕) := by
      rw [← hPS]
      exact sub_lt_self _ (by positivity)
    obtain ⟨v, ⟨g, hg, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (h𝓕.nonempty.image _) h1
    exact ⟨g, hg, hv⟩
  choose fj hfj𝓕 hfjval using hopt
  -- running maxima of the near-optimal members
  set cseq : ℕ → X → ℝ := fun n ↦ maxUpTo' (fun i ↦ fj i n) n with hcseq_def
  have hcseq_mem : ∀ n, cseq n ∈ 𝓕 := fun n ↦ maxUpTo'_mem h𝓕 (fun i ↦ hfj𝓕 i n) n
  have hcseq_dom : ∀ j n : ℕ, j ≤ n → ∀ y, fj j n y ≤ cseq n y := by
    intro j n hjn y
    rw [hcseq_def]
    exact le_maxUpTo' (f := fun i ↦ fj i n) hjn y
  -- boundedness of the approximating suprema (via the local bound `M`)
  have hbddW : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) → ∀ w ∈ ball c r,
      BddAbove (range fun n ↦ perronSeq' e c r b n (e.symm w)) := fun b hb w hw ↦
    ⟨M, by
      rintro v ⟨n, rfl⟩
      exact hMbound _ (perronSeq'_mem h𝓕 hd hb n) w hw⟩
  -- harmonicity of the suprema (Harnack's principle)
  have hWharm : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) →
      HarmonicOnNhd (fun w ↦ ⨆ n, perronSeq' e c r b n (e.symm w)) (ball c r) := by
    intro b hb
    refine harmonicOnNhd_ciSup_of_monotone' (M := M) isOpen_ball (fun n ↦ ?_) ?_ ?_
    · intro w hw
      exact perronSeq'_surfaceHarmonicOn h𝓕 hd hb n e he w (hball_sub hw)
    · intro w hw m n hmn
      exact perronSeq'_mono h𝓕 hd hb hmn (e.symm w) (hBmem w hw)
    · intro n w hw
      exact ⟨h𝓕.nonneg _ (perronSeq'_mem h𝓕 hd hb n) _ (hBmem w hw),
        hMbound _ (perronSeq'_mem h𝓕 hd hb n) w hw⟩
  -- the suprema are dominated by the Perron envelope
  have hWle : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) → ∀ w ∈ ball c r,
      (⨆ n, perronSeq' e c r b n (e.symm w)) ≤ perronSup 𝓕 (e.symm w) := by
    intro b hb w hw
    refine ciSup_le fun n ↦ ?_
    rw [hPS]
    exact le_csSup (hPSbddB w hw) ⟨_, perronSeq'_mem h𝓕 hd hb n, rfl⟩
  -- at the dense points, any supremum built from a dominating sequence attains
  -- the envelope
  have hWge : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) →
      (∀ j n : ℕ, j ≤ n → ∀ y, fj j n y ≤ b n y) → ∀ j : ℕ,
      (⨆ n, perronSeq' e c r b n (e.symm (zs j))) = perronSup 𝓕 (e.symm (zs j)) := by
    intro b hb hdom j
    refine le_antisymm (hWle b hb (zs j) (hzs_mem j)) ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    set m := Max.max j n with hm_def
    have h1 := hfjval j m
    have h2 : fj j m (e.symm (zs j)) ≤ b m (e.symm (zs j)) :=
      hdom j m (le_max_left j n) _
    have h3 : b m (e.symm (zs j)) ≤ perronSeq' e c r b m (e.symm (zs j)) :=
      le_perronSeq' h𝓕 hd hb m _ (hBmem (zs j) (hzs_mem j))
    have h4 : perronSeq' e c r b m (e.symm (zs j))
        ≤ ⨆ k, perronSeq' e c r b k (e.symm (zs j)) :=
      le_ciSup (hbddW b hb (zs j) (hzs_mem j)) m
    have h5 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (le_max_right j n)
      linarith
    linarith
  -- the supremum for the running-maxima sequence
  have hW₁harm : HarmonicOnNhd (fun w ↦ ⨆ n, perronSeq' e c r cseq n (e.symm w))
      (ball c r) := hWharm cseq hcseq_mem
  -- the Perron envelope agrees with this harmonic function on the disk
  have hfinal : ∀ w ∈ ball c r,
      perronSup 𝓕 (e.symm w) = ⨆ n, perronSeq' e c r cseq n (e.symm w) := by
    intro w hw
    refine le_antisymm ?_ (hWle cseq hcseq_mem w hw)
    rw [hPS]
    refine csSup_le (h𝓕.nonempty.image _) ?_
    rintro v ⟨g, hg, rfl⟩
    -- the second sequence, dominating both `g` and the first sequence
    have hb₂mem : ∀ n, (fun n' y ↦ Max.max (g y) (cseq n' y)) n ∈ 𝓕 := fun n ↦
      h𝓕.max_mem _ hg _ (hcseq_mem n)
    have hb₂dom : ∀ j n : ℕ, j ≤ n → ∀ y,
        fj j n y ≤ (fun n' y ↦ Max.max (g y) (cseq n' y)) n y := fun j n hjn y ↦
      (hcseq_dom j n hjn y).trans (le_max_right _ _)
    have hW₂harm := hWharm _ hb₂mem
    -- the two suprema agree on the dense sequence, hence at `w`
    have heq : (⨆ n, perronSeq' e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w))
        = ⨆ n, perronSeq' e c r cseq n (e.symm w) := by
      have h1 : Tendsto (fun w' ↦ ⨆ n, perronSeq' e c r cseq n (e.symm w'))
          (𝓝[range zs] w) (𝓝 (⨆ n, perronSeq' e c r cseq n (e.symm w))) :=
        ((hW₁harm w hw).1.continuousAt).continuousWithinAt
      have h2 : Tendsto
          (fun w' ↦ ⨆ n, perronSeq' e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w'))
          (𝓝[range zs] w)
          (𝓝 (⨆ n, perronSeq' e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w))) :=
        ((hW₂harm w hw).1.continuousAt).continuousWithinAt
      haveI : (𝓝[range zs] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hzs_dense w hw)
      have hcongr :
          (fun w' ↦ ⨆ n, perronSeq' e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w'))
          =ᶠ[𝓝[range zs] w] fun w' ↦ ⨆ n, perronSeq' e c r cseq n (e.symm w') := by
        filter_upwards [self_mem_nhdsWithin] with w' hw'
        obtain ⟨j, rfl⟩ := hw'
        exact (hWge _ hb₂mem hb₂dom j).trans (hWge cseq hcseq_mem hcseq_dom j).symm
      exact tendsto_nhds_unique (h2.congr' hcongr) h1
    -- `g` is dominated by the second supremum
    have hgle : g (e.symm w)
        ≤ ⨆ n, perronSeq' e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w) := by
      refine le_trans (le_max_left (g (e.symm w)) (cseq 0 (e.symm w))) ?_
      refine le_trans (le_perronSeq' h𝓕 hd hb₂mem 0 _ (hBmem w hw)) ?_
      exact le_ciSup (hbddW _ hb₂mem w hw) 0
    exact le_of_le_of_eq hgle heq
  -- conclude via congruence on the open disk
  have hcongr : (perronSup 𝓕 ∘ e.symm) =ᶠ[𝓝 c]
      fun w ↦ ⨆ n, perronSeq' e c r cseq n (e.symm w) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    exact hfinal w hw
  exact (harmonicAt_congr_nhds hcongr).mpr (hW₁harm c (mem_ball_self hr))


/-- A recentered, rescaled chart at `x₀ ∈ U`: sends `x₀` to `0`, contains the
unit closed ball in its target, and its unit-disk preimage lies in `U`. -/
private theorem exists_normalized_chart {U : Set X} (hUo : IsOpen U) {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
      closedBall (0 : ℂ) 1 ⊆ e.target ∧ e.symm '' closedBall (0 : ℂ) 1 ⊆ U := by
  set e₁ := chartAt ℂ x₀ with he₁_def
  have he₁ : e₁ ∈ riemannAtlas X := chartAt_mem_riemannAtlas x₀
  have hx₀e₁ : x₀ ∈ e₁.source := mem_chart_source ℂ x₀
  set p := e₁ x₀ with hp_def
  have hpt : p ∈ e₁.target := e₁.map_source hx₀e₁
  have hsymmU : ∀ᶠ z in 𝓝 p, e₁.symm z ∈ U := by
    have hx₀U : e₁.symm p ∈ U := by rw [hp_def, e₁.left_inv hx₀e₁]; exact hx₀
    exact (e₁.continuousAt_symm hpt).preimage_mem_nhds (hUo.mem_nhds hx₀U)
  obtain ⟨s₁, hs₁, hs₁ball⟩ := Metric.eventually_nhds_iff.mp hsymmU
  obtain ⟨s₂, hs₂, hs₂ball⟩ := Metric.isOpen_iff.mp e₁.open_target p hpt
  set s := min (s₁ / 2) (s₂ / 2) with hs_def
  have hspos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_s1 : s < s₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcball_t : closedBall p s ⊆ e₁.target := by
    intro z hz
    apply hs₂ball
    rw [mem_ball]; rw [mem_closedBall] at hz
    exact lt_of_le_of_lt hz (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hcball_U : e₁.symm '' closedBall p s ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    apply hs₁ball
    rw [mem_closedBall] at hz
    exact lt_of_le_of_lt hz hs_lt_s1
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have ha : (1 / (s:ℂ)) ≠ 0 := one_div_ne_zero hsC
  obtain ⟨e, he, hsrc, hval⟩ := affine_trans_mem_riemannAtlas he₁
    (a := 1/(s:ℂ)) (b := -(1/(s:ℂ)) * p) ha
  have hx₀e : x₀ ∈ e.source := by rw [hsrc]; exact hx₀e₁
  have hex₀ : e x₀ = 0 := by rw [hval x₀ hx₀e₁, hp_def]; ring
  have hkey : ∀ w ∈ closedBall (0:ℂ) 1, ∃ x ∈ e.source, e x = w ∧ x ∈ U := by
    intro w hw
    set z := p + (s:ℂ) * w with hz_def
    have hznorm : ‖z - p‖ ≤ s := by
      have : z - p = (s:ℂ) * w := by rw [hz_def]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hspos.le]
      rw [mem_closedBall, dist_zero_right] at hw
      calc s * ‖w‖ ≤ s * 1 := by exact mul_le_mul_of_nonneg_left hw hspos.le
        _ = s := by ring
    have hzcball : z ∈ closedBall p s := by rw [mem_closedBall, dist_eq_norm]; exact hznorm
    have hzt : z ∈ e₁.target := hcball_t hzcball
    have hxs : e₁.symm z ∈ e₁.source := e₁.map_target hzt
    set x := e₁.symm z with hx_def
    refine ⟨x, by rw [hsrc]; exact hxs, ?_, hcball_U ⟨z, hzcball, rfl⟩⟩
    rw [hval x hxs, hx_def, e₁.right_inv hzt, hz_def]
    field_simp
    ring
  refine ⟨e, he, hx₀e, hex₀, ?_, ?_⟩
  · intro w hw
    obtain ⟨x, hxe, hex, _⟩ := hkey w hw
    rw [← hex]; exact e.map_source hxe
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hxe, hex, hxU⟩ := hkey w hw
    rw [show e.symm w = x from by rw [← hex, e.left_inv hxe]]
    exact hxU

/-- The round open annulus in `ℂ` is preconnected (exponential image of a
convex vertical strip). -/
private theorem isPreconnected_norm_annulus {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    IsPreconnected {w : ℂ | r₁ < ‖w‖ ∧ ‖w‖ < r₂} := by
  have himg : {w : ℂ | r₁ < ‖w‖ ∧ ‖w‖ < r₂}
      = Complex.exp '' {z : ℂ | Real.log r₁ < z.re ∧ z.re < Real.log r₂} := by
    ext w
    constructor
    · rintro ⟨hw₁, hw₂⟩
      have hw0 : w ≠ 0 := by
        intro h; rw [h, norm_zero] at hw₁; linarith
      refine ⟨Complex.log w, ⟨?_, ?_⟩, Complex.exp_log hw0⟩
      · rw [Complex.log_re]; exact Real.log_lt_log h₁ hw₁
      · rw [Complex.log_re]; exact Real.log_lt_log (norm_pos_iff.mpr hw0) hw₂
    · rintro ⟨z, ⟨hz₁, hz₂⟩, rfl⟩
      rw [mem_setOf_eq, Complex.norm_exp]
      constructor
      · calc r₁ = Real.exp (Real.log r₁) := (Real.exp_log h₁).symm
          _ < Real.exp z.re := Real.exp_lt_exp.mpr hz₁
      · calc Real.exp z.re < Real.exp (Real.log r₂) := Real.exp_lt_exp.mpr hz₂
          _ = r₂ := Real.exp_log h₂
  have hconv : Convex ℝ {z : ℂ | Real.log r₁ < z.re ∧ z.re < Real.log r₂} := by
    rw [show {z : ℂ | Real.log r₁ < z.re ∧ z.re < Real.log r₂}
        = {z : ℂ | Real.log r₁ < z.re} ∩ {z : ℂ | z.re < Real.log r₂} from rfl]
    exact (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  rw [himg]
  exact hconv.isPreconnected.image _ Complex.continuous_exp.continuousOn

/-- In a locally connected space, connected components of an open set are
relatively closed: a closure point inside the ambient open set belongs to the
component. -/
private theorem mem_connectedComponentIn_of_mem_closure {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] {F : Set α} (hF : IsOpen F) {x y : α}
    (hy : y ∈ closure (connectedComponentIn F x)) (hyF : y ∈ F) :
    y ∈ connectedComponentIn F x := by
  have hC'o : IsOpen (connectedComponentIn F y) := hF.connectedComponentIn
  have hne : (connectedComponentIn F y ∩ connectedComponentIn F x).Nonempty :=
    _root_.mem_closure_iff.mp hy _ hC'o (mem_connectedComponentIn hyF)
  obtain ⟨z, hz₁, hz₂⟩ := hne
  have h1 : connectedComponentIn F x = connectedComponentIn F z := connectedComponentIn_eq hz₂
  have h2 : connectedComponentIn F y = connectedComponentIn F z := connectedComponentIn_eq hz₁
  rw [h1, ← h2]
  exact mem_connectedComponentIn hyF

/-- **Strong maximum principle**: a surface-harmonic function bounded above by
`M` that attains `M` at a point is constantly `M` on the connected component
(in `s`) of that point. -/
private theorem surfaceHarmonicOn_eqOn_const_component {u : X → ℝ} {s : Set X}
    (hs : IsOpen s) (hu : SurfaceHarmonicOn u s) {M : ℝ} (hle : ∀ x ∈ s, u x ≤ M)
    {y : X} (hy : y ∈ s) (huy : u y = M) :
    EqOn u (fun _ ↦ M) (connectedComponentIn s y) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  have hCo : IsOpen (connectedComponentIn s y) := hs.connectedComponentIn
  have hCs : connectedComponentIn s y ⊆ s := connectedComponentIn_subset s y
  have hCpc : IsPreconnected (connectedComponentIn s y) := isPreconnected_connectedComponentIn
  -- locally, the maximum set is a neighbourhood of each of its points
  have hTopen : ∀ t ∈ s, u t = M → ∀ᶠ z in 𝓝 t, u z = M := by
    intro t hts hut
    set et := chartAt ℂ t with het_def
    have het : et ∈ riemannAtlas X := chartAt_mem_riemannAtlas t
    have htsrc : t ∈ et.source := mem_chart_source ℂ t
    have hharm : HarmonicOnNhd (u ∘ et.symm) (chartImage et s) := hu et het
    have hmem : et t ∈ chartImage et s := mem_chartImage_of_mem hts htsrc
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage et hs) _ hmem
    have hsm : SubMeanOn (u ∘ et.symm) (ball (et t) ρ) :=
      (HarmonicOnNhd.meanEqOn (fun z hz ↦ hharm z (hball hz))).subMeanOn
    have hmax : IsMaxOn (u ∘ et.symm) (ball (et t) ρ) (et t) := by
      intro w hw
      have hws : et.symm w ∈ s := mapsTo_symm_chartImage (hball hw)
      simp only [Function.comp_apply, et.left_inv htsrc]
      calc u (et.symm w) ≤ M := hle _ hws
        _ = u t := hut.symm
    have heq := hsm.eqOn_const_of_isMaxOn isOpen_ball (convex_ball _ _).isPreconnected
      (mem_ball_self hρ) hmax
    have hball_t : ball (et t) ρ ⊆ et.target := hball.trans (chartImage_subset_target et s)
    have hVo : IsOpen (et.symm '' ball (et t) ρ) :=
      et.symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hball_t)
    have htV : t ∈ et.symm '' ball (et t) ρ := ⟨et t, mem_ball_self hρ, et.left_inv htsrc⟩
    filter_upwards [hVo.mem_nhds htV]
    rintro _ ⟨w, hw, rfl⟩
    have h1 := heq hw
    simp only [Function.comp_apply, et.left_inv htsrc] at h1
    rw [h1, hut]
  intro x hx
  by_contra hne
  have hopen₁ : IsOpen {z | z ∈ s ∧ u z = M} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzs, hzeq⟩
    filter_upwards [hs.mem_nhds hzs, hTopen z hzs hzeq] with w hws hweq
    exact ⟨hws, hweq⟩
  have hopen₂ : IsOpen {z | z ∈ s ∧ u z ≠ M} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzs, hzne⟩
    have hcont : ContinuousAt u z := hu.continuousOn.continuousAt (hs.mem_nhds hzs)
    filter_upwards [hs.mem_nhds hzs, hcont.eventually_ne hzne] with w hws hwne
    exact ⟨hws, hwne⟩
  have hcover : connectedComponentIn s y ⊆ {z | z ∈ s ∧ u z = M} ∪ {z | z ∈ s ∧ u z ≠ M} := by
    intro z hz
    by_cases h : u z = M
    · exact Or.inl ⟨hCs hz, h⟩
    · exact Or.inr ⟨hCs hz, h⟩
  have hne₁ : (connectedComponentIn s y ∩ {z | z ∈ s ∧ u z = M}).Nonempty :=
    ⟨y, mem_connectedComponentIn hy, hy, huy⟩
  have hne₂ : (connectedComponentIn s y ∩ {z | z ∈ s ∧ u z ≠ M}).Nonempty :=
    ⟨x, hx, hCs hx, hne⟩
  obtain ⟨w, _, ⟨_, hw₁⟩, ⟨_, hw₂⟩⟩ := hCpc _ _ hopen₁ hopen₂ hcover hne₁ hne₂
  exact hw₂ hw₁

/-! ## Step 1: the auxiliary Dirichlet solution -/

/-- The Dirichlet solution `h₁` on `W = U \ Dhalf` with boundary data `1` on
the inner circle and `0` on `frontier U`, extended by `1` across `Dhalf`. -/
private theorem exists_h1_basic [T2Space X]
    {U : Set X} (hUo : IsOpen U) (hUc : IsCompact (closure U))
    (hfr : (frontier U).Nonempty)
    (hreg : ∀ ξ ∈ frontier U, ExteriorDiskAt U ξ)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X)
    (htgt : closedBall (0 : ℂ) 1 ⊆ e.target)
    (hDU : e.symm '' closedBall (0 : ℂ) 1 ⊆ U) :
    ∃ h1 : X → ℝ,
      SurfaceHarmonicOn h1 (U \ e.symm '' closedBall 0 (1/2)) ∧
      ContinuousOn h1 (closure U) ∧
      (∀ x ∈ closure U, h1 x ∈ Icc (0:ℝ) 1) ∧
      (∀ x ∈ e.symm '' closedBall 0 (1/2), h1 x = 1) ∧
      ∀ ξ ∈ frontier U, h1 ξ = 0 := by
  classical
  set Dh := e.symm '' closedBall (0:ℂ) (1/2) with hDh_def
  set Bh := e.symm '' ball (0:ℂ) (1/2) with hBh_def
  set Sin := e.symm '' sphere (0:ℂ) (1/2) with hSin_def
  set W := U \ Dh with hW_def
  have hcb_half : closedBall (0:ℂ) (1/2) ⊆ closedBall 0 1 :=
    closedBall_subset_closedBall (by norm_num)
  have htgt_half : closedBall (0:ℂ) (1/2) ⊆ e.target := hcb_half.trans htgt
  have hDh_cpt : IsCompact Dh :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using htgt_half))
  have hDh_cl : IsClosed Dh := hDh_cpt.isClosed
  have hDhU : Dh ⊆ U := (image_mono hcb_half).trans hDU
  have hWo : IsOpen W := hUo.sdiff hDh_cl
  have he_eq : ∀ w ∈ closedBall (0:ℂ) 1, e (e.symm w) = w := fun w hw ↦ e.right_inv (htgt hw)
  have hmem_e : ∀ x ∈ Dh, x ∈ e.source ∧ ‖e x‖ ≤ 1/2 := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨e.map_target (htgt_half hw), ?_⟩
    rw [he_eq w (hcb_half hw)]
    exact mem_closedBall_zero_iff.mp hw
  have hmem_sin : ∀ x ∈ Sin, x ∈ e.source ∧ ‖e x‖ = 1/2 := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ closedBall (0:ℂ) (1/2) := sphere_subset_closedBall hw
    refine ⟨e.map_target (htgt_half hw'), ?_⟩
    rw [he_eq w (hcb_half hw')]
    exact mem_sphere_zero_iff_norm.mp hw
  have hBh_o : IsOpen Bh :=
    e.symm.isOpen_image_of_subset_source isOpen_ball
      (by simpa using (ball_subset_closedBall.trans htgt_half))
  have hBh_Dh : Bh ⊆ Dh := image_mono ball_subset_closedBall
  have hclW_Bh : closure W ⊆ Bhᶜ :=
    closure_minimal (fun x hx hB ↦ hx.2 (hBh_Dh hB)) hBh_o.isClosed_compl
  have hDh_clW : ∀ x ∈ Dh, x ∈ closure W → x ∈ Sin := by
    rintro _ ⟨w, hw, rfl⟩ hcl
    have hlt : ¬ (‖w‖ < 1/2) := by
      intro hlt
      exact hclW_Bh hcl ⟨w, mem_ball_zero_iff.mpr hlt, rfl⟩
    have hle : ‖w‖ ≤ 1/2 := mem_closedBall_zero_iff.mp hw
    exact ⟨w, mem_sphere_zero_iff_norm.mpr (le_antisymm hle (not_lt.mp hlt)), rfl⟩
  have hfrUW : ∀ ξ ∈ frontier U, ξ ∉ W ∧ ξ ∉ Dh := by
    intro ξ hξ
    have hξU : ξ ∉ U := by
      rw [frontier, hUo.interior_eq] at hξ; exact hξ.2
    exact ⟨fun h ↦ hξU h.1, fun h ↦ hξU (hDhU h)⟩
  -- `frontier U ⊆ frontier W`
  have hfrU_sub : frontier U ⊆ frontier W := by
    intro ξ hξ
    obtain ⟨hξW, hξDh⟩ := hfrUW ξ hξ
    rw [hWo.frontier_eq]
    refine ⟨?_, hξW⟩
    rw [_root_.mem_closure_iff]
    intro o ho hξo
    have hξclU : ξ ∈ closure U := frontier_subset_closure hξ
    have h1 : ((o ∩ Dhᶜ) ∩ U).Nonempty :=
      _root_.mem_closure_iff.mp hξclU _ (ho.inter hDh_cl.isOpen_compl) ⟨hξo, hξDh⟩
    obtain ⟨y, ⟨hyo, hyDh⟩, hyU⟩ := h1
    exact ⟨y, hyo, hyU, hyDh⟩
  -- the inner sphere lies in `frontier W` (radial approach from outside)
  have hSin_frW : Sin ⊆ frontier W := by
    rintro _ ⟨w, hw, rfl⟩
    have hwnorm : ‖w‖ = 1/2 := mem_sphere_zero_iff_norm.mp hw
    have hwcb : w ∈ closedBall (0:ℂ) (1/2) := sphere_subset_closedBall hw
    have hwt : w ∈ e.target := htgt_half hwcb
    rw [hWo.frontier_eq]
    constructor
    · -- closure point via the radial family `t ↦ e.symm ((1+t)·w)`
      have htend : Tendsto (fun t : ℝ ↦ e.symm (((1 + t : ℝ) : ℂ) * w)) (𝓝[>] (0:ℝ))
          (𝓝 (e.symm w)) := by
        have hc : Continuous fun t : ℝ ↦ ((1 + t : ℝ) : ℂ) * w := by fun_prop
        have h1 : Tendsto (fun t : ℝ ↦ ((1 + t : ℝ) : ℂ) * w) (𝓝 (0:ℝ)) (𝓝 w) := by
          have h0 := hc.tendsto 0
          simpa using h0
        exact (e.continuousAt_symm hwt).tendsto.comp (h1.mono_left nhdsWithin_le_nhds)
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t (ht : t ∈ Ioo (0:ℝ) 1)
      have htnorm : ‖((1 + t : ℝ) : ℂ) * w‖ = (1 + t) * (1/2) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.1]), hwnorm]
      have hcb1 : ((1 + t : ℝ) : ℂ) * w ∈ closedBall (0:ℂ) 1 := by
        rw [mem_closedBall_zero_iff, htnorm]
        nlinarith [ht.1, ht.2]
      refine ⟨hDU ⟨_, hcb1, rfl⟩, ?_⟩
      intro hmem
      have h2 := (hmem_e _ hmem).2
      rw [he_eq _ hcb1, htnorm] at h2
      nlinarith [ht.1]
    · -- not in `W` since it lies in `Dh`
      exact fun hmem ↦ hmem.2 ⟨w, hwcb, rfl⟩
  -- frontier of `W` decomposes
  have hfrW_sub : frontier W ⊆ frontier U ∪ Sin := by
    intro ξ hξ
    rw [hWo.frontier_eq] at hξ
    obtain ⟨hξcl, hξW⟩ := hξ
    have hξclU : ξ ∈ closure U := closure_mono sdiff_subset hξcl
    by_cases hξU : ξ ∈ U
    · have hξDh : ξ ∈ Dh := by
        by_contra hcon
        exact hξW ⟨hξU, hcon⟩
      exact Or.inr (hDh_clW ξ hξDh hξcl)
    · refine Or.inl ?_
      rw [frontier, hUo.interior_eq]
      exact ⟨hξclU, hξU⟩
  have hfrW_ne : (frontier W).Nonempty := hfr.imp fun ξ hξ ↦ hfrU_sub hξ
  have hclW_cpt : IsCompact (closure W) :=
    hUc.of_isClosed_subset isClosed_closure (closure_mono sdiff_subset)
  -- exterior disk condition at every frontier point of `W`
  have hregW : ∀ ξ ∈ frontier W, ExteriorDiskAt W ξ := by
    intro ξ hξ
    rcases hfrW_sub hξ with hξU | hξSin
    · obtain ⟨e', he', hξe', c, r, hr, hcb, hdist, hout⟩ := hreg ξ hξU
      exact ⟨e', he', hξe', c, r, hr, hcb, hdist, fun x hx ↦ hout x ⟨hx.1.1, hx.2⟩⟩
    · obtain ⟨hξsrc, hξnorm⟩ := hmem_sin ξ hξSin
      refine ⟨e, he, hξsrc, 0, 1/2, by norm_num, htgt_half, ?_, ?_⟩
      · rw [dist_zero_right]; exact hξnorm
      · intro x hx hball
        have hxsrc : x ∈ e.source := hx.2
        have hxDh : x ∈ Bh := ⟨e x, hball, e.left_inv hxsrc⟩
        exact hx.1.2 (hBh_Dh hxDh)
  -- boundary data: `1` on the inner circle, `0` on `frontier U`
  set f : X → ℝ := fun x ↦ if x ∈ Dh then 1 else 0 with hf_def
  have hf01 : ∀ ξ ∈ frontier W, f ξ ∈ Icc (0:ℝ) 1 := by
    intro ξ _
    by_cases hξ : ξ ∈ Dh
    · simp [hf_def, hξ]
    · simp [hf_def, hξ]
  have hfc : ContinuousOn f (frontier W) := by
    intro ξ hξ
    by_cases hξDh : ξ ∈ Dh
    · have hev : ∀ᶠ y in 𝓝[frontier W] ξ, f y = 1 := by
        filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds (hDhU hξDh)), self_mem_nhdsWithin]
          with y hyU hyfr
        rcases hfrW_sub hyfr with hyfrU | hySin
        · exact absurd hyU (fun h ↦ (hfrUW y hyfrU).1 ⟨h, (hfrUW y hyfrU).2⟩)
        · exact if_pos (image_mono sphere_subset_closedBall hySin)
      have hfξ : f ξ = 1 := if_pos hξDh
      rw [ContinuousWithinAt, hfξ]
      exact Tendsto.congr' (by filter_upwards [hev] with y hy using hy.symm) tendsto_const_nhds
    · have hev : ∀ᶠ y in 𝓝[frontier W] ξ, f y = 0 := by
        filter_upwards [nhdsWithin_le_nhds (hDh_cl.isOpen_compl.mem_nhds hξDh)] with y hyDh
        exact if_neg hyDh
      have hfξ : f ξ = 0 := if_neg hξDh
      rw [ContinuousWithinAt, hfξ]
      exact Tendsto.congr' (by filter_upwards [hev] with y hy using hy.symm) tendsto_const_nhds
  -- solve the Dirichlet problem on `W`
  obtain ⟨u, huharm, hucont, hufr, huIcc⟩ :=
    exists_dirichlet_solution hWo hclW_cpt hfrW_ne hregW hfc
  have hne_im : (f '' frontier W).Nonempty := hfrW_ne.image f
  have hsInf0 : (0:ℝ) ≤ sInf (f '' frontier W) := by
    refine le_csInf hne_im ?_
    rintro v ⟨ξ, hξ, rfl⟩
    exact (hf01 ξ hξ).1
  have hsSup1 : sSup (f '' frontier W) ≤ 1 := by
    refine csSup_le hne_im ?_
    rintro v ⟨ξ, hξ, rfl⟩
    exact (hf01 ξ hξ).2
  have hu01 : ∀ x ∈ closure W, u x ∈ Icc (0:ℝ) 1 := by
    intro x hx
    obtain ⟨h1, h2⟩ := huIcc x hx
    exact ⟨le_trans hsInf0 h1, le_trans h2 hsSup1⟩
  have hSin1 : ∀ ξ ∈ Sin, u ξ = 1 := by
    intro ξ hξ
    rw [hufr (hSin_frW hξ)]
    exact if_pos (image_mono sphere_subset_closedBall hξ)
  have hfrU0 : ∀ ξ ∈ frontier U, u ξ = 0 := by
    intro ξ hξ
    rw [hufr (hfrU_sub hξ)]
    exact if_neg (hfrUW ξ hξ).2
  -- extend by `1` across `Dh`
  set h1 : X → ℝ := fun x ↦ if x ∈ Dh then 1 else u x with hh1_def
  have hclU_eq : closure U = closure W ∪ Dh := by
    apply Subset.antisymm
    · have hU_eq : U = W ∪ Dh := by
        ext x
        constructor
        · intro hx
          by_cases hxDh : x ∈ Dh
          · exact Or.inr hxDh
          · exact Or.inl ⟨hx, hxDh⟩
        · rintro (hx | hx)
          · exact hx.1
          · exact hDhU hx
      rw [hU_eq, closure_union, hDh_cl.closure_eq]
    · refine union_subset (closure_mono sdiff_subset) ?_
      exact hDhU.trans subset_closure
  have hh1clW : EqOn h1 u (closure W) := by
    intro x hx
    by_cases hxDh : x ∈ Dh
    · rw [hh1_def]
      simp only [if_pos hxDh]
      exact (hSin1 x (hDh_clW x hxDh hx)).symm
    · rw [hh1_def]
      simp only [if_neg hxDh]
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_⟩
  · -- harmonic on `W`
    intro e' he' z hz
    refine (harmonicAt_congr_nhds ?_).mpr (huharm e' he' z hz)
    filter_upwards [(isOpen_chartImage e' hWo).mem_nhds hz] with w hw
    have hwW : e'.symm w ∈ W := mapsTo_symm_chartImage hw
    simp only [Function.comp_apply, hh1_def, if_neg hwW.2]
  · -- continuous on `closure U`
    rw [hclU_eq]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_closure hDh_cl
    · exact hucont.congr hh1clW
    · refine (continuousOn_const (c := (1:ℝ))).congr ?_
      intro x hx
      rw [hh1_def]
      simp only [if_pos hx]
  · -- values in `[0,1]`
    intro x hx
    by_cases hxDh : x ∈ Dh
    · rw [hh1_def]; simp only [if_pos hxDh]; exact ⟨zero_le_one, le_rfl⟩
    · have hxW : x ∈ closure W := by
        rcases hclU_eq ▸ hx with h | h
        · exact h
        · exact absurd h hxDh
      rw [hh1_def]; simp only [if_neg hxDh]
      exact hu01 x hxW
  · -- `1` on `Dh`
    intro x hx
    rw [hh1_def]; simp only [if_pos hx]
  · -- `0` on `frontier U`
    intro ξ hξ
    rw [hh1_def]
    simp only [if_neg (hfrUW ξ hξ).2]
    exact hfrU0 ξ hξ

/-- Affine images of surface-harmonic functions (negated multiple). -/
private theorem surfaceHarmonicOn_neg_mul {u : X → ℝ} {s : Set X}
    (hu : SurfaceHarmonicOn u s) (b : ℝ) :
    SurfaceHarmonicOn (fun x ↦ -(b * u x)) s := by
  intro e' he' z hz
  have hb : HarmonicAt ((-b) • (u ∘ e'.symm)) z := (hu e' he' z hz).const_smul
  refine (harmonicAt_congr_nhds ?_).mpr hb
  filter_upwards with w
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `log‖e ·‖ - A` is surface-harmonic away from the chart center. -/
private theorem surfaceHarmonicOn_log_chart {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) {V : Set X} (hV : V ⊆ e.source)
    (hne : ∀ x ∈ V, e x ≠ 0) (A : ℝ) :
    SurfaceHarmonicOn (fun x ↦ Real.log ‖e x‖ - A) V := by
  refine SurfaceHarmonicOn.of_chartwise ?_
  intro x hx
  refine ⟨e, he, hV hx, ?_⟩
  have hx0 : e x ≠ 0 := hne x hx
  have hlog : HarmonicAt (fun w : ℂ ↦ Real.log ‖w‖) (e x) := by
    have h1 : AnalyticAt ℂ (fun w : ℂ ↦ w) (e x) := analyticAt_id
    exact h1.harmonicAt_log_norm hx0
  have hbase : HarmonicAt ((fun w : ℂ ↦ Real.log ‖w‖) - fun _ ↦ A) (e x) :=
    hlog.sub (harmonicAt_const A)
  refine (harmonicAt_congr_nhds ?_).mpr hbase
  filter_upwards [e.open_target.mem_nhds (e.map_source (hV hx))] with w hw
  simp only [Function.comp_apply, Pi.sub_apply]
  rw [e.right_inv hw]

/-- `-log‖e ·‖ - c` is surface-harmonic away from the chart center. -/
private theorem surfaceHarmonicOn_neg_log_chart {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) {V : Set X} (hV : V ⊆ e.source)
    (hne : ∀ x ∈ V, e x ≠ 0) (c : ℝ) :
    SurfaceHarmonicOn (fun x ↦ -Real.log ‖e x‖ - c) V := by
  refine SurfaceHarmonicOn.of_chartwise ?_
  intro x hx
  refine ⟨e, he, hV hx, ?_⟩
  have hlog : HarmonicAt (fun w : ℂ ↦ Real.log ‖w‖) (e x) := by
    have h1 : AnalyticAt ℂ (fun w : ℂ ↦ w) (e x) := analyticAt_id
    exact h1.harmonicAt_log_norm (hne x hx)
  have hbase : HarmonicAt ((fun _ : ℂ ↦ -c) - fun w : ℂ ↦ Real.log ‖w‖) (e x) :=
    (harmonicAt_const _).sub hlog
  refine (harmonicAt_congr_nhds ?_).mpr hbase
  filter_upwards [e.open_target.mem_nhds (e.map_source (hV hx))] with w hw
  simp only [Function.comp_apply, Pi.sub_apply]
  rw [e.right_inv hw]
  ring

/-! ## Step 2: the strict bound on the outer circle -/

/-- The Dirichlet solution stays strictly below `1` on the outer circle:
otherwise the strong maximum principle propagates the value `1` over a whole
component of `W`, which must reach `frontier U`, where `h₁ = 0`. -/
private theorem exists_h1_bound [T2Space X]
    {U : Set X} (hUo : IsOpen U) (hUconn : IsPreconnected U)
    (hfr : (frontier U).Nonempty)
    {x₀ : X} (hx₀ : x₀ ∈ U)
    {e : OpenPartialHomeomorph X ℂ} (_he : e ∈ riemannAtlas X)
    (hx₀e : x₀ ∈ e.source) (hex₀ : e x₀ = 0)
    (htgt : closedBall (0 : ℂ) 1 ⊆ e.target)
    (hDU : e.symm '' closedBall (0 : ℂ) 1 ⊆ U)
    {h1 : X → ℝ}
    (hharm : SurfaceHarmonicOn h1 (U \ e.symm '' closedBall 0 (1/2)))
    (hcont : ContinuousOn h1 (closure U))
    (hbd : ∀ x ∈ closure U, h1 x ∈ Icc (0:ℝ) 1)
    (hfr0 : ∀ ξ ∈ frontier U, h1 ξ = 0) :
    ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ ∀ x ∈ e.symm '' sphere 0 1, h1 x ≤ a := by
  classical
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  set Dh := e.symm '' closedBall (0:ℂ) (1/2) with hDh_def
  set Bh := e.symm '' ball (0:ℂ) (1/2) with hBh_def
  set Sin := e.symm '' sphere (0:ℂ) (1/2) with hSin_def
  set Sout := e.symm '' sphere (0:ℂ) 1 with hSout_def
  set W := U \ Dh with hW_def
  have hcb_half : closedBall (0:ℂ) (1/2) ⊆ closedBall 0 1 :=
    closedBall_subset_closedBall (by norm_num)
  have htgt_half : closedBall (0:ℂ) (1/2) ⊆ e.target := hcb_half.trans htgt
  have hDh_cpt : IsCompact Dh :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using htgt_half))
  have hDh_cl : IsClosed Dh := hDh_cpt.isClosed
  have hDhU : Dh ⊆ U := (image_mono hcb_half).trans hDU
  have hWo : IsOpen W := hUo.sdiff hDh_cl
  have hWU : W ⊆ U := sdiff_subset
  have he_eq : ∀ w ∈ closedBall (0:ℂ) 1, e (e.symm w) = w := fun w hw ↦ e.right_inv (htgt hw)
  have hmem_e : ∀ x ∈ Dh, x ∈ e.source ∧ ‖e x‖ ≤ 1/2 := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨e.map_target (htgt_half hw), ?_⟩
    rw [he_eq w (hcb_half hw)]
    exact mem_closedBall_zero_iff.mp hw
  have hBh_o : IsOpen Bh :=
    e.symm.isOpen_image_of_subset_source isOpen_ball
      (by simpa using (ball_subset_closedBall.trans htgt_half))
  have hBh_Dh : Bh ⊆ Dh := image_mono ball_subset_closedBall
  have hclW_Bh : closure W ⊆ Bhᶜ :=
    closure_minimal (fun x hx hB ↦ hx.2 (hBh_Dh hB)) hBh_o.isClosed_compl
  have hDh_clW : ∀ x ∈ Dh, x ∈ closure W → x ∈ Sin := by
    rintro _ ⟨w, hw, rfl⟩ hcl
    have hlt : ¬ (‖w‖ < 1/2) := fun hlt ↦
      hclW_Bh hcl ⟨w, mem_ball_zero_iff.mpr hlt, rfl⟩
    have hle : ‖w‖ ≤ 1/2 := mem_closedBall_zero_iff.mp hw
    exact ⟨w, mem_sphere_zero_iff_norm.mpr (le_antisymm hle (not_lt.mp hlt)), rfl⟩
  have hx₀Dh : x₀ ∈ Dh :=
    ⟨0, by simp, by rw [← hex₀]; exact e.left_inv hx₀e⟩
  -- membership of the outer circle in `W`
  have hSout_W : Sout ⊆ W := by
    rintro _ ⟨w, hw, rfl⟩
    have hw1 : w ∈ closedBall (0:ℂ) 1 := sphere_subset_closedBall hw
    refine ⟨hDU ⟨w, hw1, rfl⟩, ?_⟩
    intro hmem
    have h2 := (hmem_e _ hmem).2
    rw [he_eq w hw1, mem_sphere_zero_iff_norm.mp hw] at h2
    norm_num at h2
  -- the closure of `U` decomposes
  have hclU_eq : closure U = closure W ∪ Dh := by
    apply Subset.antisymm
    · have hU_eq : U = W ∪ Dh := by
        ext x
        constructor
        · intro hx
          by_cases hxDh : x ∈ Dh
          · exact Or.inr hxDh
          · exact Or.inl ⟨hx, hxDh⟩
        · rintro (hx | hx)
          · exact hx.1
          · exact hDhU hx
      rw [hU_eq, closure_union, hDh_cl.closure_eq]
    · refine union_subset (closure_mono sdiff_subset) ?_
      exact hDhU.trans subset_closure
  -- maximum of `h1` on the compact outer circle
  have hSout_cpt : IsCompact Sout :=
    (isCompact_sphere _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using sphere_subset_closedBall.trans htgt))
  have hSout_ne : Sout.Nonempty := ⟨e.symm 1, 1, by simp, rfl⟩
  have hSout_clU : Sout ⊆ closure U := (hSout_W.trans hWU).trans subset_closure
  obtain ⟨xm, hxm, hmax⟩ := hSout_cpt.exists_isMaxOn hSout_ne (hcont.mono hSout_clU)
  refine ⟨h1 xm, (hbd xm (hSout_clU hxm)).1, ?_, fun x hx ↦ isMaxOn_iff.mp hmax x hx⟩
  -- strictness
  by_contra hcon
  push Not at hcon
  have hxm1 : h1 xm = 1 := le_antisymm (hbd xm (hSout_clU hxm)).2 hcon
  have hxmW : xm ∈ W := hSout_W hxm
  have hle1 : ∀ x ∈ W, h1 x ≤ 1 := fun x hxW ↦ (hbd x (subset_closure (hWU hxW))).2
  have hC1 : EqOn h1 (fun _ ↦ (1:ℝ)) (connectedComponentIn W xm) :=
    surfaceHarmonicOn_eqOn_const_component hWo hharm hle1 hxmW hxm1
  set C := connectedComponentIn W xm with hC_def
  have hCW : C ⊆ W := connectedComponentIn_subset W xm
  have hCo : IsOpen C := hWo.connectedComponentIn
  have hxmC : xm ∈ C := mem_connectedComponentIn hxmW
  -- a set on which `h1 ≡ 1` cannot reach `frontier U` in its closure
  have hcontra : ∀ S : Set X, S ⊆ closure U → EqOn h1 (fun _ ↦ (1:ℝ)) S →
      ∀ η ∈ frontier U, η ∈ closure S → False := by
    intro S hSclU hS1 η hη hηcl
    haveI : (𝓝[S] η).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hηcl
    have h1tend : Tendsto h1 (𝓝[S] η) (𝓝 (h1 η)) := by
      have hηclU : η ∈ closure U := frontier_subset_closure hη
      exact (hcont η hηclU).mono_left (nhdsWithin_mono η hSclU)
    have h2tend : Tendsto h1 (𝓝[S] η) (𝓝 1) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hS1 hy).symm
    have := tendsto_nhds_unique h1tend h2tend
    rw [hfr0 η hη] at this
    norm_num at this
  -- Case A: the closure of `C` meets `frontier U`
  by_cases hcase : (closure C ∩ frontier U).Nonempty
  · obtain ⟨η, hη₁, hη₂⟩ := hcase
    exact hcontra C ((hCW.trans hWU).trans subset_closure) hC1 η hη₂ hη₁
  · -- Case B: `closure C ⊆ U`; propagate `C` around the inner disk
    rw [not_nonempty_iff_eq_empty] at hcase
    have hclC_clU : closure C ⊆ closure U :=
      closure_minimal ((hCW.trans hWU).trans subset_closure) isClosed_closure
    have hclC_U : closure C ⊆ U := by
      intro y hy
      by_cases hyU : y ∈ U
      · exact hyU
      · exfalso
        have hyfr : y ∈ frontier U := by
          rw [frontier, hUo.interior_eq]
          exact ⟨hclC_clU hy, hyU⟩
        exact absurd (mem_inter hy hyfr) (by rw [hcase]; exact notMem_empty y)
    have hCrelcl : ∀ y ∈ closure C, y ∈ W → y ∈ C := fun y hy hyW ↦
      mem_connectedComponentIn_of_mem_closure hWo hy hyW
    have hfrC_Dh : ∀ y ∈ closure C, y ∉ C → y ∈ Dh := by
      intro y hy hyC
      have hyU : y ∈ U := hclC_U hy
      by_contra hyDh
      exact hyC (hCrelcl y hy ⟨hyU, hyDh⟩)
    -- the frontier of `C` is nonempty (else `C` is clopen and `U = C`)
    by_cases hfrC : (closure C \ C).Nonempty
    · -- there is a frontier point of `C`; it lies on the inner circle
      obtain ⟨ζ, hζcl, hζC⟩ := hfrC
      have hζDh : ζ ∈ Dh := hfrC_Dh ζ hζcl hζC
      have hζSin : ζ ∈ Sin := hDh_clW ζ hζDh (closure_mono hCW hζcl)
      obtain ⟨v, hv, hζv⟩ := hζSin
      have hvnorm : ‖v‖ = 1/2 := mem_sphere_zero_iff_norm.mp hv
      -- the disk of radius `2/3` and the annulus `1/2 < ‖·‖ < 2/3`
      have hb23cb : ball (0:ℂ) (2/3) ⊆ closedBall 0 1 :=
        ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
      set B23 := e.symm '' ball (0:ℂ) (2/3) with hB23_def
      have hB23_o : IsOpen B23 :=
        e.symm.isOpen_image_of_subset_source isOpen_ball
          (by simpa using hb23cb.trans htgt)
      set A_X := e.symm '' {w : ℂ | 1/2 < ‖w‖ ∧ ‖w‖ < 2/3} with hAX_def
      have hann_sub : {w : ℂ | 1/2 < ‖w‖ ∧ ‖w‖ < 2/3} ⊆ closedBall (0:ℂ) 1 := by
        intro w hw
        rw [mem_closedBall_zero_iff]
        linarith [hw.2]
      have hA_pc : IsPreconnected A_X :=
        (isPreconnected_norm_annulus (by norm_num) (by norm_num)).image _
          (e.symm.continuousOn.mono (by simpa using hann_sub.trans htgt))
      have hA_W : A_X ⊆ W := by
        rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
        refine ⟨hDU ⟨w, hann_sub ⟨hw1, hw2⟩, rfl⟩, ?_⟩
        intro hmem
        have h2 := (hmem_e _ hmem).2
        rw [he_eq w (hann_sub ⟨hw1, hw2⟩)] at h2
        linarith
      -- points of `B23 ∩ W` lie in the annulus image
      have hB23W_A : ∀ y ∈ B23, y ∈ W → y ∈ A_X := by
        rintro _ ⟨u, hu, rfl⟩ hyW
        have hu23 : ‖u‖ < 2/3 := mem_ball_zero_iff.mp hu
        have hu12 : 1/2 < ‖u‖ := by
          by_contra hle
          exact hyW.2 ⟨u, mem_closedBall_zero_iff.mpr (not_lt.mp hle), rfl⟩
        exact ⟨u, ⟨hu12, hu23⟩, rfl⟩
      -- `C` meets the annulus near `ζ`
      have hζB23 : ζ ∈ B23 := ⟨v, mem_ball_zero_iff.mpr (by rw [hvnorm]; norm_num), hζv⟩
      obtain ⟨y, hyB, hyC⟩ :=
        _root_.mem_closure_iff.mp hζcl B23 hB23_o hζB23
      have hyA : y ∈ A_X := hB23W_A y hyB (hCW hyC)
      -- hence the whole annulus lies in `C`
      have hA_C : A_X ⊆ C := by
        have h1 : A_X ⊆ connectedComponentIn W y :=
          hA_pc.subset_connectedComponentIn hyA hA_W
        rwa [← connectedComponentIn_eq (hyC : y ∈ connectedComponentIn W xm)] at h1
      have hB23_CDh : B23 ⊆ C ∪ Dh := by
        rintro _ ⟨u, hu, rfl⟩
        by_cases hle : ‖u‖ ≤ 1/2
        · exact Or.inr ⟨u, mem_closedBall_zero_iff.mpr hle, rfl⟩
        · exact Or.inl (hA_C ⟨u, ⟨not_le.mp hle, mem_ball_zero_iff.mp hu⟩, rfl⟩)
      have hDh_B23 : Dh ⊆ B23 := image_mono (closedBall_subset_ball (by norm_num))
      -- partition `U` by the open sets `C ∪ B23` and `W \ closure C`
      set O₁ := C ∪ B23 with hO₁_def
      set O₂ := W ∩ (closure C)ᶜ with hO₂_def
      have hO₁o : IsOpen O₁ := hCo.union hB23_o
      have hO₂o : IsOpen O₂ := hWo.inter isClosed_closure.isOpen_compl
      have hcover : U ⊆ O₁ ∪ O₂ := by
        intro x hxU
        by_cases hxDh : x ∈ Dh
        · exact Or.inl (Or.inr (hDh_B23 hxDh))
        · have hxW : x ∈ W := ⟨hxU, hxDh⟩
          by_cases hxcl : x ∈ closure C
          · exact Or.inl (Or.inl (hCrelcl x hxcl hxW))
          · exact Or.inr ⟨hxW, hxcl⟩
      have hdisj : O₁ ∩ O₂ = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        rintro z ⟨hz₁, hz₂⟩
        have hzW : z ∈ W := hz₂.1
        have hzncl : z ∉ closure C := hz₂.2
        rcases hz₁ with hzC | hzB
        · exact hzncl (subset_closure hzC)
        · rcases hB23_CDh hzB with hzC | hzDh
          · exact hzncl (subset_closure hzC)
          · exact hzW.2 hzDh
      by_cases hO₂ne : (U ∩ O₂).Nonempty
      · obtain ⟨z, _, hz⟩ := hUconn O₁ O₂ hO₁o hO₂o hcover
          ⟨x₀, hx₀, Or.inr (hDh_B23 hx₀Dh)⟩ hO₂ne
        rw [hdisj] at hz
        exact notMem_empty z hz
      · -- `W ⊆ C`, so `h1 ≡ 1` on `W`, contradicting the frontier values
        have hWC : W ⊆ C := by
          intro z hzW
          by_contra hzC
          by_cases hzcl : z ∈ closure C
          · exact hzC (hCrelcl z hzcl hzW)
          · exact hO₂ne ⟨z, hWU hzW, hzW, hzcl⟩
        obtain ⟨η, hη⟩ := hfr
        have hηclW : η ∈ closure W := by
          have hηclU : η ∈ closure U := frontier_subset_closure hη
          have hηDh : η ∉ Dh := by
            intro hmem
            rw [frontier, hUo.interior_eq] at hη
            exact hη.2 (hDhU hmem)
          rcases hclU_eq ▸ hηclU with h | h
          · exact h
          · exact absurd h hηDh
        exact hcontra W (hWU.trans subset_closure) (fun z hz ↦ hC1 (hWC hz)) η hη hηclW
    · -- empty frontier: `C` is clopen, contradicting preconnectedness of `U`
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hfrC
      have hCcl : IsClosed C := by
        have : closure C = C := Subset.antisymm hfrC subset_closure
        rw [← this]; exact isClosed_closure
      obtain ⟨z, _, hz₁, hz₂⟩ := hUconn C Cᶜ hCo hCcl.isOpen_compl
        (fun x _ ↦ or_not_of_imp (fun h ↦ h))
        ⟨xm, hWU hxmW, hxmC⟩
        ⟨x₀, hx₀, fun hmem ↦ (hCW hmem).2 hx₀Dh⟩
      exact hz₂ hz₁

/-! ## Step 3: the subharmonic comparison function -/

/-- The Anghel–Stan comparison function `h`: equal to `log‖e ·‖ - A` on the
inner disk, to `-B·h₁` outside the unit disk, glued by a `max` on the annulus,
with constants `B·a < A < B - log 2`. -/
private theorem exists_comparison [T2Space X]
    {U : Set X} (hUo : IsOpen U)
    {x₀ : X} (_hx₀ : x₀ ∈ U)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X)
    (hx₀e : x₀ ∈ e.source) (hex₀ : e x₀ = 0)
    (htgt : closedBall (0 : ℂ) 1 ⊆ e.target)
    (hDU : e.symm '' closedBall (0 : ℂ) 1 ⊆ U)
    {h1 : X → ℝ}
    (hharm : SurfaceHarmonicOn h1 (U \ e.symm '' closedBall 0 (1/2)))
    (hcont : ContinuousOn h1 (closure U))
    (hbd : ∀ x ∈ closure U, h1 x ∈ Icc (0:ℝ) 1)
    (hDh1 : ∀ x ∈ e.symm '' closedBall 0 (1/2), h1 x = 1)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hbdout : ∀ x ∈ e.symm '' sphere 0 1, h1 x ≤ a) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∃ h : X → ℝ,
      SurfaceSubharmonicOn h (U \ {x₀}) ∧
      ContinuousOn h (closure U \ {x₀}) ∧
      (∀ x ∈ closure U \ {x₀}, h x ≤ 0) ∧
      (∀ x ∈ e.symm '' closedBall 0 (1/2), h x = Real.log ‖e x‖ - A) ∧
      (∀ x, x ∉ e.symm '' closedBall 0 1 → h x = -(B * h1 x)) := by
  classical
  set Dh := e.symm '' closedBall (0:ℂ) (1/2) with hDh_def
  set Bh := e.symm '' ball (0:ℂ) (1/2) with hBh_def
  set D := e.symm '' closedBall (0:ℂ) 1 with hD_def
  set W := U \ Dh with hW_def
  -- constants
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set B := (Real.log 2 + 1) / (1 - a) with hB_def
  have hBpos : 0 < B := div_pos (by linarith) (by linarith)
  have hkey : B * (1 - a) = Real.log 2 + 1 := by
    rw [hB_def, div_mul_cancel₀ _ (sub_ne_zero.mpr ha1.ne')]
  set A := B - Real.log 2 - 1/2 with hA_def
  have hBa : B * a = B - Real.log 2 - 1 := by nlinarith [hkey]
  have hBaA : B * a < A := by rw [hA_def, hBa]; linarith
  have hAB : A < B - Real.log 2 := by rw [hA_def]; linarith
  have hB1 : Real.log 2 + 1 ≤ B := by nlinarith [hkey, hBpos]
  have hApos : 0 < A := by rw [hA_def]; linarith
  refine ⟨A, B, hApos, hBpos, ?_⟩
  -- geometry
  have hcb_half : closedBall (0:ℂ) (1/2) ⊆ closedBall 0 1 :=
    closedBall_subset_closedBall (by norm_num)
  have htgt_half : closedBall (0:ℂ) (1/2) ⊆ e.target := hcb_half.trans htgt
  have hDh_cpt : IsCompact Dh :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using htgt_half))
  have hD_cpt : IsCompact D :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using htgt))
  have hDh_cl : IsClosed Dh := hDh_cpt.isClosed
  have hD_cl : IsClosed D := hD_cpt.isClosed
  have hDhD : Dh ⊆ D := image_mono hcb_half
  have hDhU : Dh ⊆ U := hDhD.trans hDU
  have hWo : IsOpen W := hUo.sdiff hDh_cl
  have he_eq : ∀ w ∈ closedBall (0:ℂ) 1, e (e.symm w) = w := fun w hw ↦ e.right_inv (htgt hw)
  have hmem_eD : ∀ x ∈ D, x ∈ e.source ∧ ‖e x‖ ≤ 1 := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨e.map_target (htgt hw), ?_⟩
    rw [he_eq w hw]
    exact mem_closedBall_zero_iff.mp hw
  have hmem_e : ∀ x ∈ Dh, x ∈ e.source ∧ ‖e x‖ ≤ 1/2 := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨e.map_target (htgt_half hw), ?_⟩
    rw [he_eq w (hcb_half hw)]
    exact mem_closedBall_zero_iff.mp hw
  have hD_of : ∀ y, y ∈ e.source → ‖e y‖ ≤ 1 → y ∈ D := fun y h1' h2' ↦
    ⟨e y, mem_closedBall_zero_iff.mpr h2', e.left_inv h1'⟩
  have hDh_of : ∀ y, y ∈ e.source → ‖e y‖ ≤ 1/2 → y ∈ Dh := fun y h1' h2' ↦
    ⟨e y, mem_closedBall_zero_iff.mpr h2', e.left_inv h1'⟩
  have hBh_o : IsOpen Bh :=
    e.symm.isOpen_image_of_subset_source isOpen_ball
      (by simpa using (ball_subset_closedBall.trans htgt_half))
  have hBh_Dh : Bh ⊆ Dh := image_mono ball_subset_closedBall
  have hx₀D : x₀ ∈ D := ⟨0, by simp, by rw [← hex₀]; exact e.left_inv hx₀e⟩
  have hne0 : ∀ x ∈ D, x ≠ x₀ → e x ≠ 0 := by
    intro x hxD hxne hcon
    apply hxne
    have h1' := e.left_inv (hmem_eD x hxD).1
    have h2' := e.left_inv hx₀e
    rw [← h1', hcon, ← hex₀, h2']
  -- the pieces
  set lgA : X → ℝ := fun x ↦ Real.log ‖e x‖ - A with hlgA_def
  set nB : X → ℝ := fun x ↦ -(B * h1 x) with hnB_def
  set h : X → ℝ := fun x ↦
    if x ∈ Dh then lgA x else if x ∈ D then max (nB x) (lgA x) else nB x with hh_def
  have hh_Dh : ∀ x ∈ Dh, h x = lgA x := fun x hx ↦ if_pos hx
  have hh_out : ∀ x, x ∉ D → h x = nB x := by
    intro x hx
    rw [hh_def]
    simp only [if_neg (fun hc ↦ hx (hDhD hc)), if_neg hx]
  have hh_ann : ∀ x, x ∈ D → x ∉ Dh → h x = max (nB x) (lgA x) := by
    intro x hxD hxDh
    rw [hh_def]
    simp only [if_neg hxDh, if_pos hxD]
  -- continuity of the pieces
  have hcont_h1_at : ∀ y ∈ U, ContinuousAt h1 y := fun y hy ↦
    hcont.continuousAt (mem_of_superset (hUo.mem_nhds hy) subset_closure)
  have hcont_nB_at : ∀ y ∈ U, ContinuousAt nB y := fun y hy ↦ by
    have := (hcont_h1_at y hy).const_smul (c := B)
    have h2 := this.neg
    refine h2.congr ?_
    filter_upwards with z
    simp [hnB_def, smul_eq_mul]
  have hcont_lgA_at : ∀ y ∈ e.source, e y ≠ 0 → ContinuousAt lgA y := by
    intro y hy hne
    have hn : ContinuousAt (fun z ↦ ‖e z‖) y := (e.continuousAt hy).norm
    have hlog : ContinuousAt (fun z ↦ Real.log ‖e z‖) y := hn.log (norm_ne_zero_iff.mpr hne)
    exact hlog.sub continuousAt_const
  -- subharmonicity, by locality
  have hsub : SurfaceSubharmonicOn h (U \ {x₀}) := by
    refine SurfaceSubharmonicOn.of_locally ?_
    rintro x ⟨hxU, hxx₀'⟩
    have hxx₀ : x ≠ x₀ := by simpa using hxx₀'
    by_cases hxD : x ∈ D
    · have hxsrc : x ∈ e.source := (hmem_eD x hxD).1
      have hxnorm : ‖e x‖ ≤ 1 := (hmem_eD x hxD).2
      have hex_ne : e x ≠ 0 := hne0 x hxD hxx₀
      rcases lt_or_eq_of_le hxnorm with hlt1 | heq1
      · rcases lt_trichotomy ‖e x‖ (1/2) with hlt | heq | hgt
        · -- interior of the small disk
          refine ⟨Bh \ {x₀}, hBh_o.sdiff isClosed_singleton,
            ⟨⟨e x, mem_ball_zero_iff.mpr hlt, e.left_inv hxsrc⟩, hxx₀'⟩, ?_, ?_⟩
          · intro y hy
            exact ⟨hDhU (hBh_Dh hy.1), hy.2⟩
          · refine surfaceSubharmonicOn_congr
              ((surfaceHarmonicOn_log_chart he ?_ ?_ A).surfaceSubharmonicOn) ?_
            · intro y hy; exact (hmem_e y (hBh_Dh hy.1)).1
            · intro y hy
              exact hne0 y (hDhD (hBh_Dh hy.1)) (by simpa using hy.2)
            · intro y hy
              exact hh_Dh y (hBh_Dh hy.1)
        · -- the inner seam: `h = lgA` on a neighbourhood
          set V₂ := {y | y ∈ e.source ∧ y ∈ U ∧ y ≠ x₀ ∧ ‖e y‖ < 1 ∧ nB y < lgA y} with hV₂_def
          have hV₂o : IsOpen V₂ := by
            rw [isOpen_iff_mem_nhds]
            rintro y ⟨hy1, hy2, hy3, hy4, hy5⟩
            have hey_ne : e y ≠ 0 := hne0 y (hD_of y hy1 hy4.le) hy3
            have hcy : ContinuousAt (fun z ↦ ‖e z‖) y := (e.continuousAt hy1).norm
            have hgap : ContinuousAt (fun z ↦ lgA z - nB z) y :=
              (hcont_lgA_at y hy1 hey_ne).sub (hcont_nB_at y hy2)
            filter_upwards [e.open_source.mem_nhds hy1, hUo.mem_nhds hy2,
              isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hy3),
              hcy (Iio_mem_nhds hy4),
              hgap (Ioi_mem_nhds (sub_pos.mpr hy5))]
              with z hz1 hz2 hz3 hz4 hz5
            exact ⟨hz1, hz2, by simpa using hz3, mem_Iio.mp hz4, sub_pos.mp (mem_Ioi.mp hz5)⟩
          have hxV₂ : x ∈ V₂ := by
            refine ⟨hxsrc, hxU, hxx₀, hlt1, ?_⟩
            have hxDh : x ∈ Dh := hDh_of x hxsrc heq.le
            have h1x : h1 x = 1 := hDh1 x hxDh
            rw [hnB_def, hlgA_def]
            simp only [h1x, mul_one, heq]
            rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from one_div 2, Real.log_inv]
            linarith
          refine ⟨V₂, hV₂o, hxV₂, ?_, ?_⟩
          · intro y hy
            exact ⟨hy.2.1, by simpa using hy.2.2.1⟩
          · refine surfaceSubharmonicOn_congr
              ((surfaceHarmonicOn_log_chart he ?_ ?_ A).surfaceSubharmonicOn) ?_
            · intro y hy; exact hy.1
            · intro y hy
              exact hne0 y (hD_of y hy.1 hy.2.2.2.1.le) hy.2.2.1
            · intro y hy
              obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
              by_cases hyDh : y ∈ Dh
              · exact hh_Dh y hyDh
              · rw [hh_ann y (hD_of y hy1 hy4.le) hyDh]
                exact max_eq_right hy5.le
        · -- the annulus: `h = max (nB) (lgA)`
          set V₃ := {y | y ∈ e.source ∧ y ∈ U ∧ 1/2 < ‖e y‖ ∧ ‖e y‖ < 1} with hV₃_def
          have hV₃o : IsOpen V₃ := by
            rw [isOpen_iff_mem_nhds]
            rintro y ⟨hy1, hy2, hy3, hy4⟩
            have hcy : ContinuousAt (fun z ↦ ‖e z‖) y := (e.continuousAt hy1).norm
            filter_upwards [e.open_source.mem_nhds hy1, hUo.mem_nhds hy2,
              hcy (Ioi_mem_nhds hy3), hcy (Iio_mem_nhds hy4)] with z hz1 hz2 hz3 hz4
            exact ⟨hz1, hz2, mem_Ioi.mp hz3, mem_Iio.mp hz4⟩
          have hV₃ne : ∀ y ∈ V₃, y ≠ x₀ := by
            rintro y ⟨_, _, hy3, _⟩ hcon
            rw [hcon, hex₀, norm_zero] at hy3
            linarith
          have hV₃W : V₃ ⊆ W := by
            intro y hy
            refine ⟨hy.2.1, fun hmem ↦ ?_⟩
            linarith [(hmem_e y hmem).2, hy.2.2.1]
          refine ⟨V₃, hV₃o, ⟨hxsrc, hxU, hgt, hlt1⟩, ?_, ?_⟩
          · intro y hy
            exact ⟨hy.2.1, by simpa using hV₃ne y hy⟩
          · have hnB_harm : SurfaceHarmonicOn nB V₃ := by
              have := surfaceHarmonicOn_neg_mul (hharm.mono hV₃W) B
              exact this
            have hlg_harm : SurfaceHarmonicOn lgA V₃ :=
              surfaceHarmonicOn_log_chart he (fun y hy ↦ hy.1)
                (fun y hy ↦ hne0 y (hD_of y hy.1 hy.2.2.2.le) (hV₃ne y hy)) A
            refine surfaceSubharmonicOn_congr
              (hnB_harm.surfaceSubharmonicOn.max hlg_harm.surfaceSubharmonicOn) ?_
            intro y hy
            refine hh_ann y (hD_of y hy.1 hy.2.2.2.le) ?_
            intro hmem
            linarith [(hmem_e y hmem).2, hy.2.2.1]
      · -- the outer seam: `h = nB` on a neighbourhood
        set V₄ := {y | y ∈ e.source ∧ y ∈ U ∧ 1/2 < ‖e y‖ ∧ lgA y < nB y} with hV₄_def
        have hV₄ne : ∀ y ∈ V₄, y ≠ x₀ := by
          rintro y ⟨_, _, hy3, _⟩ hcon
          rw [hcon, hex₀, norm_zero] at hy3
          linarith
        have hV₄o : IsOpen V₄ := by
          rw [isOpen_iff_mem_nhds]
          rintro y ⟨hy1, hy2, hy3, hy4⟩
          have hey_ne : e y ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hy3
            linarith
          have hcy : ContinuousAt (fun z ↦ ‖e z‖) y := (e.continuousAt hy1).norm
          have hgap : ContinuousAt (fun z ↦ nB z - lgA z) y :=
            (hcont_nB_at y hy2).sub (hcont_lgA_at y hy1 hey_ne)
          filter_upwards [e.open_source.mem_nhds hy1, hUo.mem_nhds hy2,
            hcy (Ioi_mem_nhds hy3),
            hgap (Ioi_mem_nhds (sub_pos.mpr hy4))] with z hz1 hz2 hz3 hz4
          exact ⟨hz1, hz2, mem_Ioi.mp hz3, sub_pos.mp (mem_Ioi.mp hz4)⟩
        have hxV₄ : x ∈ V₄ := by
          refine ⟨hxsrc, hxU, by rw [heq1]; norm_num, ?_⟩
          have hxSout : x ∈ e.symm '' sphere (0:ℂ) 1 :=
            ⟨e x, mem_sphere_zero_iff_norm.mpr heq1, e.left_inv hxsrc⟩
          have h1a : h1 x ≤ a := hbdout x hxSout
          rw [hlgA_def, hnB_def]
          simp only
          rw [heq1, Real.log_one]
          have : B * h1 x ≤ B * a := mul_le_mul_of_nonneg_left h1a hBpos.le
          linarith
        refine ⟨V₄, hV₄o, hxV₄, ?_, ?_⟩
        · intro y hy
          exact ⟨hy.2.1, by simpa using hV₄ne y hy⟩
        · have hV₄W : V₄ ⊆ W := by
            intro y hy
            refine ⟨hy.2.1, fun hmem ↦ ?_⟩
            linarith [(hmem_e y hmem).2, hy.2.2.1]
          have hnB_harm : SurfaceHarmonicOn nB V₄ :=
            surfaceHarmonicOn_neg_mul (hharm.mono hV₄W) B
          refine surfaceSubharmonicOn_congr hnB_harm.surfaceSubharmonicOn ?_
          intro y hy
          by_cases hyD : y ∈ D
          · have hyDh : y ∉ Dh := fun hmem ↦ by
              linarith [(hmem_e y hmem).2, hy.2.2.1]
            rw [hh_ann y hyD hyDh]
            exact max_eq_left hy.2.2.2.le
          · exact hh_out y hyD
    · -- outside the unit disk: `h = nB`
      set V₅ := U ∩ Dᶜ with hV₅_def
      have hV₅o : IsOpen V₅ := hUo.inter hD_cl.isOpen_compl
      have hV₅W : V₅ ⊆ W := fun y hy ↦ ⟨hy.1, fun hmem ↦ hy.2 (hDhD hmem)⟩
      refine ⟨V₅, hV₅o, ⟨hxU, hxD⟩, ?_, ?_⟩
      · intro y hy
        refine ⟨hy.1, ?_⟩
        simp only [mem_singleton_iff]
        intro hcon
        exact hy.2 (hcon ▸ hx₀D)
      · have hnB_harm : SurfaceHarmonicOn nB V₅ :=
          surfaceHarmonicOn_neg_mul (hharm.mono hV₅W) B
        refine surfaceSubharmonicOn_congr hnB_harm.surfaceSubharmonicOn ?_
        intro y hy
        exact hh_out y hy.2
  refine ⟨h, hsub, ?_, ?_, hh_Dh, hh_out⟩
  · -- continuity on `closure U \ {x₀}`
    intro x hx
    obtain ⟨hxclU, hxx₀'⟩ := hx
    by_cases hxU : x ∈ U
    · exact (hsub.continuousOn.continuousAt
        (((hUo.sdiff isClosed_singleton).mem_nhds ⟨hxU, hxx₀'⟩))).continuousWithinAt
    · -- frontier point: `h = nB` on the neighbourhood `Dᶜ`
      have hxD : x ∉ D := fun hmem ↦ hxU (hDU hmem)
      have hev : ∀ᶠ y in 𝓝 x, h y = nB y := by
        filter_upwards [hD_cl.isOpen_compl.mem_nhds hxD] with y hy
        exact hh_out y hy
      have hnB_cw : ContinuousWithinAt nB (closure U \ {x₀}) x := by
        have h1' : ContinuousWithinAt h1 (closure U \ {x₀}) x :=
          (hcont.mono sdiff_subset) x ⟨hxclU, hxx₀'⟩
        have h2' := (h1'.const_smul (c := B)).neg
        refine h2'.congr (fun y _ ↦ ?_) ?_
        · simp [hnB_def, smul_eq_mul]
        · simp [hnB_def, smul_eq_mul]
      exact hnB_cw.congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
  · -- nonpositivity
    intro x hx
    obtain ⟨hxclU, hxx₀'⟩ := hx
    have hnB_le : nB x ≤ 0 := by
      rw [hnB_def]
      simp only [neg_nonpos]
      exact mul_nonneg hBpos.le (hbd x hxclU).1
    by_cases hxDh : x ∈ Dh
    · rw [hh_Dh x hxDh]
      have hlog_le : Real.log ‖e x‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) (le_trans (hmem_e x hxDh).2 (by norm_num))
      rw [hlgA_def]
      simp only
      linarith
    · by_cases hxD : x ∈ D
      · rw [hh_ann x hxD hxDh]
        have hlog_le : Real.log ‖e x‖ ≤ 0 :=
          Real.log_nonpos (norm_nonneg _) (hmem_eD x hxD).2
        refine max_le hnB_le ?_
        rw [hlgA_def]
        simp only
        linarith
      · rw [hh_out x hxD]
        exact hnB_le

/-- `G` is a Green's function for the (relatively compact, open) set `U`
with pole at `x₀ ∈ U`. -/
structure IsGreenFunction (U : Set X) (x₀ : X) (G : X → ℝ) : Prop where
  continuousOn : ContinuousOn G (closure U \ {x₀})
  harmonicOn : SurfaceHarmonicOn G (U \ {x₀})
  pos : ∀ x ∈ U \ {x₀}, 0 < G x
  zero_frontier : EqOn G 0 (frontier U)
  /-- Logarithmic pole: in some chart centered at `x₀`, `G + log‖·‖` extends
  harmonically across the puncture. -/
  log_pole : ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : ℂ) r ⊆ e.target ∧
      e.symm '' closedBall (0 : ℂ) r ⊆ U ∧
      ∃ H : ℂ → ℝ, HarmonicOnNhd H (ball (0 : ℂ) r) ∧
        ∀ z ∈ ball (0 : ℂ) r \ {0}, G (e.symm z) = -Real.log ‖z‖ + H z

/-- **Existence of the Green's function** (Anghel–Stan Proposition 9) on a
relatively compact, connected, exterior-disk-regular open set. -/
theorem exists_green_function [T2Space X]
    {U : Set X} (hUo : IsOpen U) (hUc : IsCompact (closure U))
    (hUconn : IsPreconnected U)
    (hfr : (frontier U).Nonempty)
    (hreg : ∀ ξ ∈ frontier U, ExteriorDiskAt U ξ)
    {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∃ G : X → ℝ, IsGreenFunction U x₀ G := by
  classical
  haveI : LocallyCompactSpace X := Rado.locallyCompactSpace
  obtain ⟨e, he, hx₀e, hex₀, htgt, hDU⟩ := exists_normalized_chart hUo hx₀
  obtain ⟨h1, h1harm, h1cont, h1bd, h1Dh, h1fr⟩ :=
    exists_h1_basic hUo hUc hfr hreg he htgt hDU
  obtain ⟨a, ha0, ha1, hbdout⟩ :=
    exists_h1_bound hUo hUconn hfr hx₀ he hx₀e hex₀ htgt hDU h1harm h1cont h1bd h1fr
  obtain ⟨A, B, hApos, hBpos, h, hsub, hcnt, hle0, hDh_eq, hout_eq⟩ :=
    exists_comparison hUo hx₀ he hx₀e hex₀ htgt hDU h1harm h1cont h1bd h1Dh ha0 ha1 hbdout
  -- geometry
  set Dh := e.symm '' closedBall (0:ℂ) (1/2) with hDh_def
  set D := e.symm '' closedBall (0:ℂ) 1 with hD_def
  set s := U \ {x₀} with hs_def
  have hso : IsOpen s := hUo.sdiff isClosed_singleton
  have hcb_half : closedBall (0:ℂ) (1/2) ⊆ closedBall 0 1 :=
    closedBall_subset_closedBall (by norm_num)
  have htgt_half : closedBall (0:ℂ) (1/2) ⊆ e.target := hcb_half.trans htgt
  have hD_cpt : IsCompact D :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using htgt))
  have hD_cl : IsClosed D := hD_cpt.isClosed
  have hDhD : Dh ⊆ D := image_mono hcb_half
  have he_eq : ∀ w ∈ closedBall (0:ℂ) 1, e (e.symm w) = w := fun w hw ↦ e.right_inv (htgt hw)
  have hmem_eD : ∀ x ∈ D, x ∈ e.source ∧ ‖e x‖ ≤ 1 := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨e.map_target (htgt hw), ?_⟩
    rw [he_eq w hw]
    exact mem_closedBall_zero_iff.mp hw
  have hmem_e : ∀ x ∈ Dh, x ∈ e.source ∧ ‖e x‖ ≤ 1/2 := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨e.map_target (htgt_half hw), ?_⟩
    rw [he_eq w (hcb_half hw)]
    exact mem_closedBall_zero_iff.mp hw
  have hDh_of : ∀ y, y ∈ e.source → ‖e y‖ ≤ 1/2 → y ∈ Dh := fun y h1' h2' ↦
    ⟨e y, mem_closedBall_zero_iff.mpr h2', e.left_inv h1'⟩
  have hx₀D : x₀ ∈ D := ⟨0, by simp, by rw [← hex₀]; exact e.left_inv hx₀e⟩
  have hne0 : ∀ x ∈ D, x ≠ x₀ → e x ≠ 0 := by
    intro x hxD hxne hcon
    apply hxne
    have h1' := e.left_inv (hmem_eD x hxD).1
    have h2' := e.left_inv hx₀e
    rw [← h1', hcon, ← hex₀, h2']
  have hs_sub : s ⊆ closure U \ {x₀} := fun x hx ↦ ⟨subset_closure hx.1, hx.2⟩
  have hcl_dec : ∀ x ∈ closure U \ {x₀}, x ∈ s ∨ x ∈ frontier U := by
    rintro x ⟨hxcl, hxne⟩
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨hxU, hxne⟩
    · exact Or.inr (by rw [frontier, hUo.interior_eq]; exact ⟨hxcl, hxU⟩)
  have hfrU_nD : ∀ ξ ∈ frontier U, ξ ∉ D := by
    intro ξ hξ hmem
    rw [frontier, hUo.interior_eq] at hξ
    exact hξ.2 (hDU hmem)
  have hfrU_ne_x₀ : ∀ ξ ∈ frontier U, ξ ≠ x₀ := fun ξ hξ hcon ↦ hfrU_nD ξ hξ (hcon ▸ hx₀D)
  have hfrU_sub : frontier U ⊆ closure U \ {x₀} := fun ξ hξ ↦
    ⟨frontier_subset_closure hξ, by simpa using hfrU_ne_x₀ ξ hξ⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the family witness `αf`
  set αf : X → ℝ := fun x ↦ if x ∈ D then max (-Real.log ‖e x‖ - Real.log 2) 0 else 0
    with hαf_def
  have hα_nonneg : ∀ x, 0 ≤ αf x := by
    intro x
    rw [hαf_def]
    by_cases hx : x ∈ D
    · simp only [if_pos hx]; exact le_max_right _ _
    · simp only [if_neg hx]; exact le_rfl
  have hα_fr : ∀ ξ ∈ frontier U, αf ξ = 0 := fun ξ hξ ↦ if_neg (hfrU_nD ξ hξ)
  have hα_out : ∀ x, x ∉ D → αf x = 0 := fun x hx ↦ if_neg hx
  have hα_Dh_ge : ∀ x ∈ Dh, -Real.log ‖e x‖ - Real.log 2 ≤ αf x := by
    intro x hx
    rw [hαf_def]
    simp only [if_pos (hDhD hx)]
    exact le_max_left _ _
  have hα_zero_of_norm : ∀ x, 1/2 ≤ ‖e x‖ → αf x = 0 := by
    intro x hxn
    rw [hαf_def]
    by_cases hx : x ∈ D
    · simp only [if_pos hx]
      refine max_eq_right ?_
      have hlog : Real.log (1/2) ≤ Real.log ‖e x‖ := Real.log_le_log (by norm_num) hxn
      rw [one_div, Real.log_inv] at hlog
      linarith
    · simp only [if_neg hx]
  -- subharmonicity of `αf`
  have hconst_sub : ∀ V : Set X, SurfaceSubharmonicOn (fun _ ↦ (0:ℝ)) V := fun V ↦
    ⟨continuousOn_const, fun _ _ ↦ SubMeanOn.const⟩
  have hα_sub : SurfaceSubharmonicOn αf s := by
    refine SurfaceSubharmonicOn.of_locally ?_
    rintro x ⟨hxU, hxx₀'⟩
    have hxx₀ : x ≠ x₀ := by simpa using hxx₀'
    by_cases hxD : x ∈ D
    · have hxsrc := (hmem_eD x hxD).1
      rcases lt_or_eq_of_le (hmem_eD x hxD).2 with hlt | heq
      · -- inside the open unit disk
        set V := (e.symm '' ball (0:ℂ) 1) \ {x₀} with hV_def
        have hVo : IsOpen V :=
          (e.symm.isOpen_image_of_subset_source isOpen_ball
            (by simpa using ball_subset_closedBall.trans htgt)).sdiff isClosed_singleton
        have hVD : V ⊆ D := fun y hy ↦ image_mono ball_subset_closedBall hy.1
        have hVs : V ⊆ s := fun y hy ↦ ⟨hDU (hVD hy), hy.2⟩
        refine ⟨V, hVo, ⟨⟨e x, mem_ball_zero_iff.mpr hlt, e.left_inv hxsrc⟩, hxx₀'⟩, hVs, ?_⟩
        have hcore : SurfaceHarmonicOn (fun y ↦ -Real.log ‖e y‖ - Real.log 2) V :=
          surfaceHarmonicOn_neg_log_chart he (fun y hy ↦ (hmem_eD y (hVD hy)).1)
            (fun y hy ↦ hne0 y (hVD hy) (by simpa using hy.2)) (Real.log 2)
        refine surfaceSubharmonicOn_congr
          (hcore.surfaceSubharmonicOn.max (hconst_sub V)) ?_
        intro y hy
        exact if_pos (hVD hy)
      · -- on the unit circle: `αf ≡ 0` nearby
        set V := {y | y ∈ e.source ∧ y ∈ U ∧ 1/2 < ‖e y‖} with hV_def
        have hVo : IsOpen V := by
          rw [isOpen_iff_mem_nhds]
          rintro y ⟨hy1, hy2, hy3⟩
          have hcy : ContinuousAt (fun z ↦ ‖e z‖) y := (e.continuousAt hy1).norm
          filter_upwards [e.open_source.mem_nhds hy1, hUo.mem_nhds hy2,
            hcy (Ioi_mem_nhds hy3)] with z hz1 hz2 hz3
          exact ⟨hz1, hz2, mem_Ioi.mp hz3⟩
        have hVs : V ⊆ s := by
          rintro y ⟨hy1, hy2, hy3⟩
          refine ⟨hy2, ?_⟩
          simp only [mem_singleton_iff]
          intro hcon
          rw [hcon, hex₀, norm_zero] at hy3
          linarith
        refine ⟨V, hVo, ⟨hxsrc, hxU, by rw [heq]; norm_num⟩, hVs, ?_⟩
        refine surfaceSubharmonicOn_congr (hconst_sub V) ?_
        intro y hy
        exact hα_zero_of_norm y hy.2.2.le
    · -- outside the unit disk
      set V := U ∩ Dᶜ with hV_def
      have hVo : IsOpen V := hUo.inter hD_cl.isOpen_compl
      have hVs : V ⊆ s := by
        rintro y ⟨hy1, hy2⟩
        refine ⟨hy1, ?_⟩
        simp only [mem_singleton_iff]
        rintro rfl
        exact hy2 hx₀D
      refine ⟨V, hVo, ⟨hxU, hxD⟩, hVs, ?_⟩
      exact surfaceSubharmonicOn_congr (hconst_sub V) (fun y hy ↦ hα_out y hy.2)
  -- continuity of `αf`
  have hα_cont : ContinuousOn αf (closure U \ {x₀}) := by
    intro x hx
    rcases hcl_dec x hx with hxs | hxfr
    · exact (hα_sub.continuousOn.continuousAt (hso.mem_nhds hxs)).continuousWithinAt
    · have hev : ∀ᶠ y in 𝓝 x, αf y = (fun _ ↦ (0:ℝ)) y := by
        filter_upwards [hD_cl.isOpen_compl.mem_nhds (hfrU_nD x hxfr)] with y hy
        exact hα_out y hy
      exact (continuousWithinAt_const (b := (0:ℝ))).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) (hα_fr x hxfr)
  -- `αf + h ≤ 0`
  have hα_h : ∀ x ∈ closure U \ {x₀}, αf x + h x ≤ 0 := by
    rintro x ⟨hxcl, hxne'⟩
    by_cases hxDh : x ∈ Dh
    · have hheq := hDh_eq x hxDh
      have hlogle : Real.log ‖e x‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) ((hmem_e x hxDh).2.trans (by norm_num))
      have hαle : αf x ≤ -h x := by
        rw [hαf_def, hheq]
        simp only [if_pos (hDhD hxDh)]
        refine max_le (by linarith) (by linarith)
      linarith
    · have hα0 : αf x = 0 := by
        by_cases hxD : x ∈ D
        · refine hα_zero_of_norm x ?_
          by_contra hlt
          exact hxDh (hDh_of x (hmem_eD x hxD).1 (not_le.mp hlt).le)
        · exact hα_out x hxD
      rw [hα0, zero_add]
      exact hle0 x ⟨hxcl, hxne'⟩
  -- the Perron family
  set 𝓕 : Set (X → ℝ) := {g | SurfaceSubharmonicOn g s ∧ ContinuousOn g (closure U \ {x₀}) ∧
      (∀ x ∈ closure U \ {x₀}, 0 ≤ g x) ∧ (∀ ξ ∈ frontier U, g ξ = 0) ∧
      ∀ x ∈ closure U \ {x₀}, g x + h x ≤ 0} with h𝓕_def
  have hα𝓕 : αf ∈ 𝓕 := ⟨hα_sub, hα_cont, fun x _ ↦ hα_nonneg x, hα_fr, hα_h⟩
  have hfrU_notU : ∀ ξ ∈ frontier U, ξ ∉ U := by
    intro ξ hξ
    rw [frontier, hUo.interior_eq] at hξ
    exact hξ.2
  -- the family is a locally bounded Perron family
  have hLB : LocBoundedPerronFamily 𝓕 s := by
    constructor
    · exact ⟨αf, hα𝓕⟩
    · exact fun g hg ↦ hg.1
    · exact fun g hg x hx ↦ hg.2.2.1 x (hs_sub hx)
    · -- local boundedness by `-h` on a compact neighbourhood
      intro x hx
      obtain ⟨K, hKcpt, hxK, hKs⟩ := exists_compact_subset hso hx
      refine ⟨interior K, isOpen_interior, hxK, ?_⟩
      have hKsub : K ⊆ closure U \ {x₀} := hKs.trans hs_sub
      have hKcont : ContinuousOn (fun y ↦ -h y) K := (hcnt.mono hKsub).neg
      have hbdd : BddAbove ((fun y ↦ -h y) '' K) := hKcpt.bddAbove_image hKcont
      refine ⟨sSup ((fun y ↦ -h y) '' K), ?_⟩
      rintro g hg y ⟨hyV, hys⟩
      have hyK : y ∈ K := interior_subset hyV
      have h1' : g y ≤ -h y := by linarith [hg.2.2.2.2 y (hKsub hyK)]
      exact h1'.trans (le_csSup hbdd ⟨y, hyK, rfl⟩)
    · -- closed under max
      rintro g₁ ⟨hs₁, hc₁, hn₁, hf₁, hh₁⟩ g₂ ⟨hs₂, hc₂, hn₂, hf₂, hh₂⟩
      refine ⟨hs₁.max hs₂, hc₁.sup hc₂, ?_, ?_, ?_⟩
      · exact fun x hx ↦ le_trans (hn₁ x hx) (le_max_left _ _)
      · intro ξ hξ
        show Max.max (g₁ ξ) (g₂ ξ) = 0
        rw [hf₁ ξ hξ, hf₂ ξ hξ, max_self]
      · intro x hx
        show Max.max (g₁ x) (g₂ x) + h x ≤ 0
        have h1' := hh₁ x hx
        have h2' := hh₂ x hx
        have hle : Max.max (g₁ x) (g₂ x) ≤ -h x :=
          max_le (by linarith) (by linarith)
        linarith
    · -- closed under harmonic replacement
      rintro g ⟨hgsub, hgcont, hgnn, hgfr, hgh⟩ e' c r hd
      have he' := hd.mem_atlas
      have hrpos := hd.r_pos
      have hcb_t : closedBall c r ⊆ e'.target := hd.closedBall_subset
      set K := e'.symm '' closedBall c r with hK_def
      have hKs' : K ⊆ s := hd.preimage_subset
      have hKcl : IsClosed K := hd.compact_preimage.isClosed
      have hKclU : K ⊆ closure U \ {x₀} := hKs'.trans hs_sub
      have hgsub' : SurfaceSubharmonicOn (surfaceReplace g e' c r) s :=
        surfaceReplace_surfaceSubharmonicOn hso hgsub hd
      have hsph_chart : ∀ w ∈ closedBall c r, e'.symm w ∈ K := fun w hw ↦ ⟨w, hw, rfl⟩
      have hgf : ContinuousOn (g ∘ e'.symm) (sphere c r) := by
        refine ContinuousOn.comp (hgcont.mono hKclU) ?_ ?_
        · exact e'.symm.continuousOn.mono (by simpa using sphere_subset_closedBall.trans hcb_t)
        · exact fun w hw ↦ hsph_chart w (sphere_subset_closedBall hw)
      -- the maximum-principle comparison on the replacement disk
      have hrep_h : ∀ x ∈ K, surfaceReplace g e' c r x + h x ≤ 0 := by
        rintro _ ⟨w₀, hw₀, rfl⟩
        have hsrc : e'.symm w₀ ∈ e'.source := e'.map_target (hcb_t hw₀)
        have hew : e' (e'.symm w₀) = w₀ := e'.right_inv (hcb_t hw₀)
        have hball_chart : ball c r ⊆ chartImage e' s := by
          intro w hw
          have hwcb := ball_subset_closedBall hw
          exact ⟨e'.symm w, ⟨hKs' (hsph_chart w hwcb), e'.map_target (hcb_t hwcb)⟩,
            e'.right_inv (hcb_t hwcb)⟩
        have hsm_h : SubMeanOn (h ∘ e'.symm) (ball c r) :=
          (hsub.subMeanOn e' he').mono hball_chart
        have hP_harm : HarmonicOnNhd (poissonExtension (g ∘ e'.symm) c r) (ball c r) :=
          poissonExtension_harmonicOnNhd hrpos hgf
        have hF_sm : SubMeanOn ((h ∘ e'.symm) + poissonExtension (g ∘ e'.symm) c r)
            (ball c r) := hsm_h.add_meanEq (HarmonicOnNhd.meanEqOn hP_harm)
        have hsymm_cont : ContinuousOn (e'.symm : ℂ → X) (closedBall c r) :=
          e'.symm.continuousOn.mono (by simpa using hcb_t)
        have hh_cont : ContinuousOn (h ∘ e'.symm) (closedBall c r) :=
          (hcnt.mono hKclU).comp hsymm_cont (fun w hw ↦ hsph_chart w hw)
        have hP_cont : ContinuousOn (poissonExtension (g ∘ e'.symm) c r) (closedBall c r) :=
          poissonExtension_continuousOn hrpos hgf
        have hF_cont : ContinuousOn ((h ∘ e'.symm) + poissonExtension (g ∘ e'.symm) c r)
            (closure (ball c r)) := by
          rw [closure_ball c hrpos.ne']
          exact hh_cont.add hP_cont
        have hfr_le : ∀ w ∈ frontier (ball c r),
            ((h ∘ e'.symm) + poissonExtension (g ∘ e'.symm) c r) w ≤ 0 := by
          intro w hw
          rw [frontier_ball c hrpos.ne'] at hw
          have hwcb := sphere_subset_closedBall hw
          have hPw : poissonExtension (g ∘ e'.symm) c r w = (g ∘ e'.symm) w :=
            poissonExtension_eqOn_sphere hrpos hgf hw
          simp only [Pi.add_apply, Function.comp_apply, hPw]
          have := hgh (e'.symm w) (hKclU (hsph_chart w hwcb))
          linarith
        have hall := hF_sm.le_of_frontier_le isOpen_ball isBounded_ball hF_cont hfr_le
        have hw₀cl : w₀ ∈ closure (ball c r) := by
          rw [closure_ball c hrpos.ne']; exact hw₀
        have hFw₀ := hall w₀ hw₀cl
        simp only [Pi.add_apply, Function.comp_apply] at hFw₀
        have hrep : surfaceReplace g e' c r (e'.symm w₀)
            = poissonExtension (g ∘ e'.symm) c r w₀ := by
          simp only [surfaceReplace, hew]
          rw [dif_pos ⟨hsrc, hw₀⟩]
        rw [hrep]
        linarith
      refine ⟨hgsub', ?_, ?_, ?_, ?_⟩
      · -- continuity
        intro x hx
        rcases hcl_dec x hx with hxs | hxfr
        · exact (hgsub'.continuousOn.continuousAt (hso.mem_nhds hxs)).continuousWithinAt
        · have hxK : x ∉ K := fun hmem ↦ hfrU_notU x hxfr (hKs' hmem).1
          have hev : surfaceReplace g e' c r =ᶠ[𝓝 x] g := by
            filter_upwards [hKcl.isOpen_compl.mem_nhds hxK] with y hy
            exact surfaceReplace_eqOn_compl hy
          exact (hgcont x hx).congr_of_eventuallyEq
            (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
      · -- nonnegativity
        intro x hx
        by_cases hxK : x ∈ K
        · have hxs : x ∈ s := hKs' hxK
          exact le_trans (hgnn x hx) (le_surfaceReplace hgsub hd x hxs)
        · rw [surfaceReplace_eqOn_compl hxK]
          exact hgnn x hx
      · -- zero on the frontier
        intro ξ hξ
        have hξK : ξ ∉ K := fun hmem ↦ hfrU_notU ξ hξ (hKs' hmem).1
        rw [surfaceReplace_eqOn_compl hξK]
        exact hgfr ξ hξ
      · -- the `+ h ≤ 0` constraint
        intro x hx
        by_cases hxK : x ∈ K
        · exact hrep_h x hxK
        · rw [surfaceReplace_eqOn_compl hxK]
          exact hgh x hx
  -- the Green's function: the Perron envelope
  have hDhU : Dh ⊆ U := hDhD.trans hDU
  set G := perronSup 𝓕 with hG_def
  have hGharm : SurfaceHarmonicOn G s := hLB.surfaceHarmonicOn_perronSup hso
  have hGle : ∀ x ∈ closure U \ {x₀}, G x ≤ -h x := by
    intro x hx
    refine hLB.perronSup_le ?_
    intro g hg
    linarith [hg.2.2.2.2 x hx]
  have hαG : ∀ x ∈ s, αf x ≤ G x := hLB.le_perronSup hα𝓕
  have hG0 : ∀ ξ ∈ frontier U, G ξ = 0 := by
    intro ξ hξ
    have himg : (fun g ↦ g ξ) '' 𝓕 = {(0:ℝ)} := by
      apply Subset.antisymm
      · rintro v ⟨g, hg, rfl⟩
        simp only [mem_singleton_iff]
        exact hg.2.2.2.1 ξ hξ
      · rintro v hv
        rw [mem_singleton_iff] at hv
        exact ⟨αf, hα𝓕, by rw [hv]; exact hα_fr ξ hξ⟩
    rw [hG_def]
    show sSup ((fun g ↦ g ξ) '' 𝓕) = 0
    rw [himg, csSup_singleton]
  have hGnn : ∀ x ∈ closure U \ {x₀}, 0 ≤ G x := by
    intro x hx
    rcases hcl_dec x hx with hxs | hxfr
    · exact le_trans (hα_nonneg x) (hαG x hxs)
    · rw [hG0 x hxfr]
  have hGlow : ∀ x ∈ Dh, x ≠ x₀ → -Real.log ‖e x‖ - Real.log 2 ≤ G x := by
    intro x hx hne
    exact le_trans (hα_Dh_ge x hx) (hαG x ⟨hDhU hx, by simpa using hne⟩)
  refine ⟨G, ?_, hGharm, ?_, ?_, ?_⟩
  · -- continuity on `closure U \ {x₀}`
    intro x hx
    rcases hcl_dec x hx with hxs | hxfr
    · exact (hGharm.continuousOn.continuousAt (hso.mem_nhds hxs)).continuousWithinAt
    · -- squeeze `0 ≤ G ≤ B·h1` at the frontier
      rw [ContinuousWithinAt, hG0 x hxfr]
      have hh1x : h1 x = 0 := h1fr x hxfr
      have htendh1 : Tendsto (fun y ↦ B * h1 y) (𝓝[closure U \ {x₀}] x) (𝓝 0) := by
        have h1cw : ContinuousWithinAt h1 (closure U \ {x₀}) x :=
          (h1cont.mono sdiff_subset) x hx
        have := (tendsto_const_nhds (x := B)).mul h1cw
        rwa [hh1x, mul_zero] at this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htendh1 ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact hGnn y hy
      · have hDmem : Dᶜ ∈ 𝓝 x := hD_cl.isOpen_compl.mem_nhds (hfrU_nD x hxfr)
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hDmem] with y hy hyD
        have hle := hGle y hy
        rw [hout_eq y hyD] at hle
        linarith
  · -- strict positivity
    intro y hy
    have hyclU : y ∈ closure U \ {x₀} := hs_sub hy
    rcases (hGnn y hyclU).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
      have hGnegharm : SurfaceHarmonicOn (-G) s := hGharm.neg
      have hle' : ∀ x ∈ s, (-G) x ≤ 0 := fun x hx ↦ by
        simp only [Pi.neg_apply, neg_nonpos]
        exact hGnn x (hs_sub hx)
      have hyG : (-G) y = 0 := by simp only [Pi.neg_apply, ← heq, neg_zero]
      have hEq := surfaceHarmonicOn_eqOn_const_component hso hGnegharm hle' hy hyG
      have hCzero : ∀ z ∈ connectedComponentIn s y, G z = 0 := by
        intro z hz
        have := hEq hz
        simp only [Pi.neg_apply] at this
        linarith [this]
      have hCo : IsOpen (connectedComponentIn s y) := hso.connectedComponentIn
      have hCs : connectedComponentIn s y ⊆ s := connectedComponentIn_subset s y
      have hyC : y ∈ connectedComponentIn s y := mem_connectedComponentIn hy
      set Bq := e.symm '' ball (0:ℂ) (1/4) with hBq_def
      have hBq_o : IsOpen Bq := by
        refine e.symm.isOpen_image_of_subset_source isOpen_ball ?_
        have : ball (0:ℂ) (1/4) ⊆ closedBall 0 1 :=
          ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
        simpa using this.trans htgt
      have hsymm0 : e.symm (0:ℂ) = x₀ := by rw [← hex₀]; exact e.left_inv hx₀e
      have hx₀Bq : x₀ ∈ Bq := ⟨0, mem_ball_self (by norm_num), hsymm0⟩
      by_cases hx₀cl : x₀ ∈ closure (connectedComponentIn s y)
      · obtain ⟨z, hzBq, hzC⟩ := _root_.mem_closure_iff.mp hx₀cl Bq hBq_o hx₀Bq
        obtain ⟨w, hw, rfl⟩ := hzBq
        have hwn : ‖w‖ < 1/4 := mem_ball_zero_iff.mp hw
        have hzs : e.symm w ∈ s := hCs hzC
        have hzDh : e.symm w ∈ Dh := ⟨w, mem_closedBall_zero_iff.mpr (by linarith), rfl⟩
        have hzne : e.symm w ≠ x₀ := by simpa using hzs.2
        have hew : e (e.symm w) = w :=
          he_eq w (mem_closedBall_zero_iff.mpr (by linarith))
        have hlow := hGlow (e.symm w) hzDh hzne
        rw [hew] at hlow
        have hwpos : 0 < ‖w‖ := by
          rw [norm_pos_iff]
          intro hcon
          rw [hcon] at hzne
          exact hzne hsymm0
        have hlog4 : Real.log ‖w‖ < Real.log (1/4) := Real.log_lt_log hwpos hwn
        have hlogq : Real.log ((1:ℝ)/4) = -(2 * Real.log 2) := by
          rw [show (1:ℝ)/4 = ((2:ℝ)^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
          push_cast
          ring
        rw [hlogq] at hlog4
        have hGz : G (e.symm w) = 0 := hCzero _ hzC
        rw [hGz] at hlow
        linarith
      · have hCrel : ∀ z ∈ closure (connectedComponentIn s y), z ∈ s →
            z ∈ connectedComponentIn s y := fun z hz hzs ↦
          mem_connectedComponentIn_of_mem_closure hso hz hzs
        have hcover : U ⊆ connectedComponentIn s y ∪ (closure (connectedComponentIn s y))ᶜ := by
          intro v hv
          by_cases hvcl : v ∈ closure (connectedComponentIn s y)
          · left
            refine hCrel v hvcl ⟨hv, ?_⟩
            simp only [mem_singleton_iff]
            rintro rfl
            exact hx₀cl hvcl
          · right; exact hvcl
        obtain ⟨z, _, hz₁, hz₂⟩ := hUconn _ _ hCo isClosed_closure.isOpen_compl
          hcover ⟨y, hy.1, hyC⟩ ⟨x₀, hx₀, hx₀cl⟩
        exact hz₂ (subset_closure hz₁)
  · -- zero on the frontier
    intro ξ hξ
    simp only [Pi.zero_apply]
    exact hG0 ξ hξ
  · -- the logarithmic pole
    have hz_ne : ∀ z ∈ ball (0:ℂ) (1/2) \ {(0:ℂ)}, e.symm z ≠ x₀ := by
      intro z hz hcon
      have hz2 : z ∈ closedBall (0:ℂ) (1/2) := ball_subset_closedBall hz.1
      have hew := he_eq z (hcb_half hz2)
      rw [hcon, hex₀] at hew
      exact (by simpa using hz.2 : z ≠ 0) hew.symm
    have hchart : ∀ z ∈ ball (0:ℂ) (1/2) \ {(0:ℂ)}, z ∈ chartImage e s := by
      intro z hz
      have hz2 : z ∈ closedBall (0:ℂ) (1/2) := ball_subset_closedBall hz.1
      have hzDh : e.symm z ∈ Dh := ⟨z, hz2, rfl⟩
      exact ⟨e.symm z, ⟨⟨hDhU hzDh, by simpa using hz_ne z hz⟩, (hmem_e _ hzDh).1⟩,
        he_eq z (hcb_half hz2)⟩
    set u : ℂ → ℝ := fun z ↦ G (e.symm z) + Real.log ‖z‖ with hu_def
    have hu_harm : HarmonicOnNhd u (ball (0:ℂ) (1/2) \ {0}) := by
      intro z hz
      have h1' : HarmonicAt (G ∘ e.symm) z := hGharm e he z (hchart z hz)
      have h2' : HarmonicAt (fun w : ℂ ↦ Real.log ‖w‖) z := by
        have haz : AnalyticAt ℂ (fun w : ℂ ↦ w) z := analyticAt_id
        exact haz.harmonicAt_log_norm (by simpa using hz.2)
      have hsum : HarmonicAt ((G ∘ e.symm) + fun w : ℂ ↦ Real.log ‖w‖) z := h1'.add h2'
      refine (harmonicAt_congr_nhds ?_).mpr hsum
      filter_upwards with w
      simp [hu_def]
    have hu_bdd : ∀ z ∈ ball (0:ℂ) (1/2) \ {0}, |u z| ≤ max A (Real.log 2) := by
      intro z hz
      have hz2 : z ∈ closedBall (0:ℂ) (1/2) := ball_subset_closedBall hz.1
      have hzDh : e.symm z ∈ Dh := ⟨z, hz2, rfl⟩
      have hew : e (e.symm z) = z := he_eq z (hcb_half hz2)
      have hzne := hz_ne z hz
      have hcl : e.symm z ∈ closure U \ {x₀} :=
        ⟨subset_closure (hDhU hzDh), by simpa using hzne⟩
      have hup : G (e.symm z) ≤ A - Real.log ‖z‖ := by
        have hle := hGle _ hcl
        rw [hDh_eq _ hzDh, hew] at hle
        linarith
      have hlo : -Real.log ‖z‖ - Real.log 2 ≤ G (e.symm z) := by
        have hge := hGlow _ hzDh hzne
        rwa [hew] at hge
      rw [hu_def, abs_le]
      constructor
      · simp only
        have h2' : -(max A (Real.log 2)) ≤ -Real.log 2 := neg_le_neg (le_max_right _ _)
        linarith
      · simp only
        have h2' : A ≤ max A (Real.log 2) := le_max_left _ _
        linarith
    obtain ⟨H, hH_harm, hH_eq⟩ := exists_harmonicOnNhd_extension_of_bounded
      (by norm_num : (0:ℝ) < 1/2) hu_harm hu_bdd
    refine ⟨e, he, hx₀e, hex₀, 1/2, by norm_num, htgt_half, hDhU, H, hH_harm, ?_⟩
    intro z hz
    have hzeq := hH_eq hz
    simp only [hu_def] at hzeq
    linarith

end

end Uniformization
