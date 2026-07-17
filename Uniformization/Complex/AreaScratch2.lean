import Uniformization.Complex.AreaIntegral

open Set Metric Complex MeasureTheory Topology Filter Real intervalIntegral

noncomputable section

namespace Uniformization

variable {h : ℂ → ℂ} {b : ℕ → ℂ}
  (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (h z))

include hb

/-- **C2 (positivity).**  `0 ≤ Re (shoelace h t)` for `t > 1`, via the winding-number
indicator dichotomy off the null image circle. -/
theorem shoelace_re_nonneg (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (hinj : Set.InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    {t : ℝ} (ht : 1 < t) : 0 ≤ (shoelace h t).re := by
  have ht0 : 0 < t := lt_trans one_pos ht
  -- Laurent tail bounds discharged at t₁ = (1+t)/2
  set t₁ : ℝ := (1 + t) / 2 with ht₁def
  have ht₁ : 1 < t₁ := by rw [ht₁def]; linarith
  have hgrow := extMap_grow_bound hb ht₁
  have hnum := extMap_num_bound hb ht₁
  -- analyticity / continuity of the curve
  have hsub : sphere (0 : ℂ) t ⊆ exteriorUnit := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    simp only [exteriorUnit, mem_setOf_eq, hw]; exact ht
  have hGA : AnalyticOnNhd ℂ (extMap h) exteriorUnit := extMap_analyticOnNhd h hh
  have hGcont : ContinuousOn (extMap h) (sphere (0 : ℂ) t) := hGA.continuousOn.mono hsub
  -- choose R
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) t).exists_bound_of_continuousOn hGcont
  set R : ℝ := M + 1 with hRdef
  have hcurve : ∀ θ : ℝ, ‖extMap h (circleMap 0 t θ)‖ < R := by
    intro θ
    have hmem : circleMap 0 t θ ∈ sphere (0 : ℂ) t := circleMap_mem_sphere 0 ht0.le θ
    have := hM _ hmem
    rw [hRdef]; linarith
  -- image circle is null
  have hdiff : DifferentiableOn ℝ (extMap h) (sphere (0 : ℂ) t) :=
    ((hGA.differentiableOn).mono hsub).restrictScalars ℝ
  have hnull : volume (extMap h '' sphere (0 : ℂ) t) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume hdiff (MeasureTheory.Measure.addHaar_sphere volume 0 t)
  -- reduce to the area integral of winding
  rw [← integral_winding_eq_shoelace h hh ht hcurve]
  -- pointwise dichotomy off the curve
  have hpt : ∀ p : ℂ, p ∉ extMap h '' sphere (0 : ℂ) t → 0 ≤ (winding h t p).re := by
    intro p hp
    by_cases hpre : ∃ w : ℂ, t ≤ ‖w‖ ∧ extMap h w = p
    · obtain ⟨w, hwt, hwp⟩ := hpre
      have hwgt : t < ‖w‖ := by
        rcases lt_or_eq_of_le hwt with hlt | heq
        · exact hlt
        · exact absurd ⟨w, by rw [mem_sphere_zero_iff_norm]; exact heq.symm, hwp⟩ hp
      rw [winding_eq_zero_of_preimage h hh hinj ht₁ hgrow hnum ht hwp hwgt]; simp
    · push_neg at hpre
      rw [winding_eq_one_of_no_preimage h hh ht₁ hgrow hnum ht (fun w hw => hpre w hw)]; simp
  -- a.e. nonnegativity of the real part
  have hae : ∀ᵐ p ∂(volume.restrict (ball (0 : ℂ) R)), 0 ≤ (winding h t p).re := by
    have hnmem : ∀ᵐ p ∂volume, p ∉ extMap h '' sphere (0 : ℂ) t := compl_mem_ae_iff.2 hnull
    exact (ae_restrict_of_ae hnmem).mono hpt
  by_cases hint : Integrable (fun p => winding h t p) (volume.restrict (ball (0 : ℂ) R))
  · have hre : (∫ p in ball (0 : ℂ) R, winding h t p).re
        = ∫ p in ball (0 : ℂ) R, (winding h t p).re := by
      rw [← integral_re hint]
    rw [hre]
    exact setIntegral_nonneg_of_ae_restrict hae
  · rw [integral_undef hint]; simp

end Uniformization
