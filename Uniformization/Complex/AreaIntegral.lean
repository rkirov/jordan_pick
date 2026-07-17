/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Complex.AreaWinding
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The area/shoelace integral identity (Stage B)

For the exterior univalent map `extMap h` (see `Uniformization/Complex/AreaWinding.lean`)
this file relates the area integral of the winding number to the shoelace contour
integral:

  `∫_{p ∈ ball 0 R} winding h t p dA(p) = shoelace h t`,

where (matching the `circleIntegral` convention `∮_{|w|=t} f = ∫₀^{2π} (i t e^{iθ})·f(t e^{iθ}) dθ`)

  `shoelace h t := (2i)⁻¹ ∮_{|w|=t} conj(extMap h w) · (extMap h)'(w) dw`,

and `R` is large enough that the image circle lies inside `ball 0 R`.

## Route (as in the design notes)

* **B1** (Cauchy transform of the disk): for `‖ζ‖ < R`,
    `∫_{p ∈ ball 0 R} (ζ − p)⁻¹ dp = π · conj ζ`.
  Proof: polar coordinates `p = r e^{iθ}` reduce this to
  `∫₀^R r · (∫₀^{2π} (ζ − r e^{iθ})⁻¹ dθ) dr`; the inner angular integral is
  `2π/ζ` for `r < ‖ζ‖` (mean-value property, `angular_lt` below) and `0` for
  `r > ‖ζ‖` (`angular_gt`, by partial fractions on the circle), so the radial
  integral is `(2π/ζ)·‖ζ‖²/2 = π·conj ζ`.
* **B2** (Fubini): unfold `winding`/`shoelace` to `intervalIntegral`s over `θ` and
  swap with the `p`-integral over `ball 0 R`.  The uncurried integrand is dominated
  by `C·‖(extMap h (t e^{iθ}) − p)‖⁻¹`, which is jointly integrable (the curve is
  compact `⊆ ball 0 R`, and `‖·‖⁻¹` is 2D-locally-integrable), so
  `MeasureTheory.integral_integral_swap` applies.
* **B3** (assembly): after the swap the inner integral is the Cauchy transform B1,
  giving `(2πi)⁻¹ ∫₀^{2π} (i t e^{iθ}) (extMap h)'(t e^{iθ}) · π conj(extMap h (t e^{iθ})) dθ
  = (2i)⁻¹ ∮ conj(extMap h) (extMap h)' = shoelace h t` (using `(2πi)⁻¹·π = (2i)⁻¹`).

## Status

**Sorry-free.**  Proved here: the shoelace definition; both angular halves of B1 —
`angular_lt` (`∫₀^{2π} (ζ − r e^{iθ})⁻¹ dθ = 2π/ζ` for `|r| < ‖ζ‖`, mean value, via
`circleAverage_of_differentiable_on_off_countable`) and `angular_gt` (`= 0` for
`‖ζ‖ < r`, via partial fractions on the circle); the Cauchy transform of the disk
`cauchyTransform_disk` (B1, polar coordinates + the angular integrals); the main
Fubini identity `integral_winding_eq_shoelace` (B2/B3); and the Laurent coefficient
infrastructure (summability, termwise derivative, tail bounds) consumed by Stage C
(`AreaEval.lean`).
-/

open Set Metric Complex MeasureTheory Topology Filter Real intervalIntegral

noncomputable section

namespace Uniformization

/-- The shoelace (Green/enclosed-area) contour integral, in the `circleIntegral`
convention: `shoelace h t = (2i)⁻¹ ∮_{|w|=t} conj(extMap h w) · (extMap h)'(w) dw`. -/
def shoelace (h : ℂ → ℂ) (t : ℝ) : ℂ :=
  (2 * I)⁻¹ * ∮ w in C(0, t), (starRingEnd ℂ) (extMap h w) * deriv (extMap h) w

/-- **Mean-value core of the Cauchy transform (B1)**: for `|ρ| < ‖ζ‖` the analytic
function `z ↦ (ζ − z)⁻¹` has circle average `1/ζ`, i.e.
`∫₀^{2π} (ζ − ρ e^{iθ})⁻¹ dθ = 2π/ζ`. -/
theorem angular_lt (ζ : ℂ) {ρ : ℝ} (hballR : |ρ| < ‖ζ‖) :
    (∫ θ in (0:ℝ)..2 * π, (ζ - circleMap 0 ρ θ)⁻¹) = 2 * ↑π / ζ := by
  have hcont : ContinuousOn (fun z => (ζ - z)⁻¹) (closedBall 0 |ρ|) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    exact sub_ne_zero.mpr fun h => by rw [← h] at hz; linarith
  have hdiff : ∀ z ∈ ball (0:ℂ) |ρ| \ (∅ : Set ℂ), DifferentiableAt ℂ (fun z => (ζ - z)⁻¹) z := by
    intro z hz
    rw [sdiff_empty, mem_ball_zero_iff] at hz
    have hzne : ζ - z ≠ 0 := sub_ne_zero.mpr fun h => by rw [← h] at hz; linarith
    exact ((differentiableAt_const ζ).sub differentiableAt_id).inv hzne
  have havg := circleAverage_of_differentiable_on_off_countable
    (c := (0:ℂ)) (R := ρ) countable_empty hcont hdiff
  rw [circleAverage_def] at havg
  simp only [sub_zero] at havg
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have h3 : (∫ θ in (0:ℝ)..2 * π, (ζ - circleMap 0 ρ θ)⁻¹) = (2 * π : ℝ) • ζ⁻¹ := by
    have hc := congrArg (fun x : ℂ => (2 * π : ℝ) • x) havg
    simp only [smul_smul, mul_inv_cancel₀ h2pi, one_smul] at hc
    exact hc
  rw [h3, Complex.real_smul]
  push_cast
  ring

/-- **Exterior case of the Cauchy transform (B1)**: for `‖ζ‖ < ρ` the circle of
radius `ρ` encloses the pole `ζ`, and `∫₀^{2π} (ζ − ρ e^{iθ})⁻¹ dθ = 0`.
Proof: convert to `∮_{|z|=ρ} (ζ − z)⁻¹ z⁻¹ dz`, then partial fractions
`(ζ − z)⁻¹ z⁻¹ = ζ⁻¹((z)⁻¹ − (z − ζ)⁻¹)` gives `ζ⁻¹(2πi − 2πi) = 0` (the `ζ = 0`
case reduces to `∮ z⁻² = 0`). -/
theorem angular_gt (ζ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρζ : ‖ζ‖ < ρ) :
    (∫ θ in (0:ℝ)..2 * π, (ζ - circleMap 0 ρ θ)⁻¹) = 0 := by
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hconv : (∮ z in C(0, ρ), (ζ - z)⁻¹ * z⁻¹)
      = I * ∫ θ in (0:ℝ)..2 * π, (ζ - circleMap 0 ρ θ)⁻¹ := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hcm : circleMap 0 ρ θ ≠ 0 := by
      rw [← norm_pos_iff, norm_circleMap_zero, abs_of_pos hρ]; exact hρ
    simp only [deriv_circleMap, smul_eq_mul]
    rw [show circleMap 0 ρ θ * I * ((ζ - circleMap 0 ρ θ)⁻¹ * (circleMap 0 ρ θ)⁻¹)
          = I * (ζ - circleMap 0 ρ θ)⁻¹ * (circleMap 0 ρ θ * (circleMap 0 ρ θ)⁻¹) from by ring,
      mul_inv_cancel₀ hcm, mul_one]
  have hci0 : (∮ z in C(0, ρ), (ζ - z)⁻¹ * z⁻¹) = 0 := by
    by_cases hζ : ζ = 0
    · subst hζ
      have heq : EqOn (fun z : ℂ => (0 - z)⁻¹ * z⁻¹) (fun z => (-1 : ℂ) * (z - 0) ^ (-2 : ℤ))
          (sphere (0:ℂ) ρ) := by
        intro z hz
        rw [mem_sphere_zero_iff_norm] at hz
        have hz0 : z ≠ 0 := by rw [← norm_pos_iff, hz]; exact hρ
        show (0 - z)⁻¹ * z⁻¹ = (-1 : ℂ) * (z - 0) ^ (-2 : ℤ)
        rw [sub_zero, zpow_neg, show ((2:ℤ)) = ((2:ℕ):ℤ) from rfl, zpow_natCast]
        field_simp
        ring
      rw [circleIntegral.integral_congr hρ.le heq, circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_zpow_of_ne (by norm_num) 0 0 ρ, mul_zero]
    · have hζball : ζ ∈ ball (0:ℂ) ρ := by rw [mem_ball_zero_iff]; exact hρζ
      have h0ball : (0:ℂ) ∈ ball (0:ℂ) ρ := by rw [mem_ball_zero_iff, norm_zero]; exact hρ
      have hci_zinv : CircleIntegrable (fun z : ℂ => (z - (0:ℂ))⁻¹) 0 ρ := by
        apply ContinuousOn.circleIntegrable hρ.le
        apply ContinuousOn.inv₀ (by fun_prop)
        intro z hz; rw [mem_sphere_zero_iff_norm] at hz
        rw [sub_zero, ← norm_pos_iff, hz]; exact hρ
      have hci_zζ : CircleIntegrable (fun z : ℂ => (z - ζ)⁻¹) 0 ρ := by
        apply ContinuousOn.circleIntegrable hρ.le
        apply ContinuousOn.inv₀ (by fun_prop)
        intro z hz; rw [mem_sphere_zero_iff_norm] at hz
        rw [sub_ne_zero]; intro h; rw [h] at hz; linarith
      have heq : EqOn (fun z : ℂ => (ζ - z)⁻¹ * z⁻¹)
          (fun z => ζ⁻¹ * ((z - (0:ℂ))⁻¹ - (z - ζ)⁻¹)) (sphere (0:ℂ) ρ) := by
        intro z hz
        rw [mem_sphere_zero_iff_norm] at hz
        have hz0 : z ≠ 0 := by rw [← norm_pos_iff, hz]; exact hρ
        have hzζ : z - ζ ≠ 0 := by rw [sub_ne_zero]; intro h; rw [h] at hz; linarith
        have hζz : ζ - z ≠ 0 := fun h => hzζ (by rw [sub_eq_zero] at h ⊢; exact h.symm)
        show (ζ - z)⁻¹ * z⁻¹ = ζ⁻¹ * ((z - (0:ℂ))⁻¹ - (z - ζ)⁻¹)
        rw [sub_zero]
        field_simp
        ring
      rw [circleIntegral.integral_congr hρ.le heq, circleIntegral.integral_const_mul,
        circleIntegral.integral_sub hci_zinv hci_zζ,
        circleIntegral.integral_sub_inv_of_mem_ball h0ball,
        circleIntegral.integral_sub_inv_of_mem_ball hζball, sub_self, mul_zero]
  rw [hconv] at hci0
  rcases mul_eq_zero.mp hci0 with h | h
  · exact absurd h hI
  · exact h

/-- **Cauchy transform of the disk (B1)**: for `‖ζ‖ < R`,
`∫_{p ∈ ball 0 R} (ζ − p)⁻¹ dp = π · conj ζ`. -/
theorem cauchyTransform_disk {ζ : ℂ} {R : ℝ} (hζR : ‖ζ‖ < R) :
    ∫ p in ball (0:ℂ) R, (ζ - p)⁻¹ = ↑π * (starRingEnd ℂ) ζ := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg ζ) hζR
  have hsymm : ∀ q : ℝ × ℝ, Complex.polarCoord.symm q = circleMap 0 q.1 q.2 := by
    intro q
    rw [Complex.polarCoord_symm_apply]
    simp only [circleMap, zero_add]
    rw [Complex.exp_mul_I]; push_cast; ring
  -- STEP 1: integrability of (ζ - ·)⁻¹ on ball 0 R
  have hint : IntegrableOn (fun p : ℂ => (ζ - p)⁻¹) (ball 0 R) volume := by
    have hbig : IntegrableOn (fun q : ℂ => q⁻¹) (ball 0 (‖ζ‖ + R)) volume := by
      refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_
      · show (1:ℕ) ≤ Module.finrank ℝ ℂ
        rw [Complex.finrank_real_complex]; norm_num
      · show (1:ℝ) < (Module.finrank ℝ ℂ : ℝ)
        rw [Complex.finrank_real_complex]; norm_num
      · filter_upwards with x
        rw [norm_inv, Real.rpow_neg_one, one_mul]
      · exact measurable_inv.aestronglyMeasurable
    have hballζ : IntegrableOn (fun q : ℂ => q⁻¹) (ball (-ζ) R) volume := by
      apply hbig.mono_set
      apply ball_subset_ball'
      rw [dist_zero_right, norm_neg]; linarith
    have hmp : MeasurePreserving (fun p : ℂ => p - ζ) volume volume :=
      measurePreserving_sub_right volume ζ
    have hme : MeasurableEmbedding (fun p : ℂ => p - ζ) :=
      (Homeomorph.subRight ζ).measurableEmbedding
    have himg : (fun p : ℂ => p - ζ) '' ball 0 R = ball (-ζ) R := by
      ext q
      simp only [mem_image, mem_ball_iff_norm]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [sub_zero] at hp
        have : p - ζ - -ζ = p := by ring
        rw [this]; exact hp
      · intro hq
        refine ⟨q + ζ, ?_, by ring⟩
        rw [sub_zero]
        have : q + ζ = q - -ζ := by ring
        rw [this]; exact hq
    have hiff := (hmp.integrableOn_image (f := fun q : ℂ => q⁻¹) (s := ball 0 R) hme)
    rw [himg] at hiff
    have hpz : IntegrableOn (fun p : ℂ => (p - ζ)⁻¹) (ball 0 R) volume := hiff.mp hballζ
    have heqfun : (fun p : ℂ => (ζ - p)⁻¹) = fun p => -((p - ζ)⁻¹) := by
      ext p
      have hpp : ζ - p = -(p - ζ) := by ring
      rw [hpp, inv_neg]
    rw [heqfun]
    exact hpz.neg
  -- STEP 2a: product integrability of the polar integrand
  have hprodint : IntegrableOn (fun q : ℝ × ℝ => q.1 • (ζ - circleMap 0 q.1 q.2)⁻¹)
      (Ioo (0:ℝ) R ×ˢ Ioo (-π) π) (volume.prod volume) := by
    set g : ℂ → ℂ := fun w => (ζ - w)⁻¹ with hg
    set hn : ℂ → ENNReal := fun p => ‖(ball (0:ℂ) R).indicator g p‖ₑ with hhn
    constructor
    · apply Measurable.aestronglyMeasurable
      have hcm : Continuous (fun q : ℝ × ℝ => circleMap 0 q.1 q.2) := by
        unfold circleMap; fun_prop
      exact measurable_fst.smul (((continuous_const.sub hcm).measurable).inv)
    · rw [hasFiniteIntegral_iff_enorm, ← Measure.volume_eq_prod]
      have hsub : (Ioo (0:ℝ) R ×ˢ Ioo (-π) π) ⊆ polarCoord.target := by
        rw [_root_.polarCoord_target]
        exact Set.prod_mono Ioo_subset_Ioi_self (le_refl _)
      calc ∫⁻ q in (Ioo (0:ℝ) R ×ˢ Ioo (-π) π), ‖q.1 • (ζ - circleMap 0 q.1 q.2)⁻¹‖ₑ ∂volume
          = ∫⁻ q in (Ioo (0:ℝ) R ×ˢ Ioo (-π) π),
              ENNReal.ofReal q.1 • hn (Complex.polarCoord.symm q) ∂volume := by
            apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
            intro q hq
            have hr : (0:ℝ) < q.1 := hq.1.1
            have hlt : q.1 < R := hq.1.2
            have hmem : circleMap 0 q.1 q.2 ∈ ball (0:ℂ) R := by
              rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr]; exact hlt
            show ‖q.1 • (ζ - circleMap 0 q.1 q.2)⁻¹‖ₑ
                = ENNReal.ofReal q.1 • hn (Complex.polarCoord.symm q)
            rw [hhn]
            simp only [hsymm, indicator_of_mem hmem, hg]
            rw [enorm_smul, enorm_of_nonneg hr.le, smul_eq_mul]
        _ ≤ ∫⁻ q in polarCoord.target,
              ENNReal.ofReal q.1 • hn (Complex.polarCoord.symm q) ∂volume :=
            lintegral_mono_set hsub
        _ = ∫⁻ p, hn p := Complex.lintegral_comp_polarCoord_symm hn
        _ = ∫⁻ p in ball (0:ℂ) R, ‖g p‖ₑ ∂volume := by
            simp only [hhn]
            rw [← lintegral_indicator measurableSet_ball]
            congr 1
            funext p
            by_cases hp : p ∈ ball (0:ℂ) R
            · rw [indicator_of_mem hp, indicator_of_mem hp]
            · rw [indicator_of_notMem hp, indicator_of_notMem hp, enorm_zero]
        _ < ⊤ := by
            have hfi := hint.hasFiniteIntegral
            rw [hasFiniteIntegral_iff_enorm] at hfi
            exact hfi
  -- STEP 2b: polar change of variables reduces LHS to the product integral
  have hpolar : ∫ p in ball (0:ℂ) R, (ζ - p)⁻¹
      = ∫ q in (Ioo (0:ℝ) R ×ˢ Ioo (-π) π), q.1 • (ζ - circleMap 0 q.1 q.2)⁻¹ := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    rw [← Complex.integral_comp_polarCoord_symm
        (fun w => (ball (0:ℂ) R).indicator (fun z => (ζ - z)⁻¹) w)]
    rw [_root_.polarCoord_target]
    rw [← MeasureTheory.integral_indicator (measurableSet_Ioi.prod measurableSet_Ioo),
        ← MeasureTheory.integral_indicator ((measurableSet_Ioo).prod measurableSet_Ioo)]
    congr 1
    funext q
    by_cases hq : q ∈ Ioo (0:ℝ) R ×ˢ Ioo (-π) π
    · have hqi : q ∈ Ioi (0:ℝ) ×ˢ Ioo (-π) π := ⟨hq.1.1, hq.2⟩
      rw [indicator_of_mem hqi, indicator_of_mem hq, hsymm]
      have hr : (0:ℝ) < q.1 := hq.1.1
      have hmem : circleMap 0 q.1 q.2 ∈ ball (0:ℂ) R := by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr]; exact hq.1.2
      rw [indicator_of_mem hmem]
    · rw [indicator_of_notMem hq]
      by_cases hqi : q ∈ Ioi (0:ℝ) ×ˢ Ioo (-π) π
      · rw [indicator_of_mem hqi, hsymm]
        have hr : (0:ℝ) < q.1 := hqi.1
        have hnotmem : circleMap 0 q.1 q.2 ∉ ball (0:ℂ) R := by
          rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr, not_lt]
          by_contra hlt
          exact hq ⟨⟨hr, lt_of_not_ge hlt⟩, hqi.2⟩
        rw [indicator_of_notMem hnotmem, smul_zero]
      · rw [indicator_of_notMem hqi]
  -- STEP 2c: iterate the product integral and reduce the inner integral to `0..2π`
  have hiter : ∫ q in (Ioo (0:ℝ) R ×ˢ Ioo (-π) π), q.1 • (ζ - circleMap 0 q.1 q.2)⁻¹
      = ∫ r in Ioo (0:ℝ) R, r • (∫ θ in (0:ℝ)..2*π, (ζ - circleMap 0 r θ)⁻¹) ∂volume := by
    rw [Measure.volume_eq_prod ℝ ℝ, setIntegral_prod _ hprodint]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    show ∫ θ in Ioo (-π) π, r • (ζ - circleMap 0 r θ)⁻¹ ∂volume
        = r • ∫ θ in (0:ℝ)..2*π, (ζ - circleMap 0 r θ)⁻¹
    rw [MeasureTheory.integral_smul]
    congr 1
    have hper : Function.Periodic (fun θ => (ζ - circleMap 0 r θ)⁻¹) (2 * π) := by
      intro θ; simp only; rw [periodic_circleMap 0 r θ]
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : (-π:ℝ) ≤ π)]
    have hshift := hper.intervalIntegral_add_eq (-π) 0
    rw [show (-π) + 2*π = π by ring, show (0:ℝ) + 2*π = 2*π by ring] at hshift
    rw [hshift]
  -- STEP 3: radial computation using `angular_lt` / `angular_gt`
  rw [hpolar, hiter]
  by_cases hζ0 : ζ = 0
  · subst hζ0
    simp only [map_zero, mul_zero]
    have hz : (∫ r in Ioo (0:ℝ) R, r • (∫ θ in (0:ℝ)..2*π, ((0:ℂ) - circleMap 0 r θ)⁻¹) ∂volume)
        = ∫ r in Ioo (0:ℝ) R, (0:ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      have hr0 : 0 < r := hr.1
      show r • (∫ θ in (0:ℝ)..2*π, ((0:ℂ) - circleMap 0 r θ)⁻¹) = 0
      rw [angular_gt (0:ℂ) hr0 (by rw [norm_zero]; exact hr0), smul_zero]
    rw [hz, MeasureTheory.integral_zero]
  · have hζpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    set g2 : ℝ → ℂ := fun s => (2 * ↑π / ζ) * (s:ℂ) with hg2
    have hpne : ∀ᵐ r ∂(volume:Measure ℝ), r ≠ ‖ζ‖ := by
      rw [ae_iff]; simp only [not_not]
      rw [show {r : ℝ | r = ‖ζ‖} = {‖ζ‖} from by ext x; simp]
      exact Real.volume_singleton
    have hae : (fun r => r • (∫ θ in (0:ℝ)..2*π, (ζ - circleMap 0 r θ)⁻¹))
        =ᵐ[volume.restrict (Ioo (0:ℝ) R)] (Ioo (0:ℝ) ‖ζ‖).indicator g2 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hpne] with r hrne hrin
      have hr0 : 0 < r := hrin.1
      rcases lt_or_gt_of_ne hrne with hlt | hgt
      · rw [angular_lt ζ (by rw [abs_of_pos hr0]; exact hlt),
            indicator_of_mem (show r ∈ Ioo (0:ℝ) ‖ζ‖ from ⟨hr0, hlt⟩), hg2, Complex.real_smul]
        ring
      · rw [angular_gt ζ hr0 hgt, smul_zero,
            indicator_of_notMem (show r ∉ Ioo (0:ℝ) ‖ζ‖ from
              fun h => absurd h.2 (not_lt.mpr hgt.le))]
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.setIntegral_indicator measurableSet_Ioo]
    rw [show (Ioo (0:ℝ) R) ∩ (Ioo (0:ℝ) ‖ζ‖) = Ioo (0:ℝ) ‖ζ‖ from
        inter_eq_right.mpr (Ioo_subset_Ioo (le_refl 0) hζR.le)]
    rw [hg2]
    simp only
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ r in Ioo (0:ℝ) ‖ζ‖, (r:ℂ)) = ((↑(‖ζ‖^2/2 : ℝ)) : ℂ) from by
        rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hζpos.le,
            intervalIntegral.integral_ofReal, integral_id]; push_cast; ring]
    have hns : (↑(‖ζ‖^2) : ℂ) = ζ * (starRingEnd ℂ) ζ := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have he : ((((‖ζ‖^2/2 : ℝ)) : ℂ)) = (↑(‖ζ‖^2):ℂ)/2 := by push_cast; ring
    rw [he, hns]; field_simp

/-- **The area/shoelace integral identity (Stage B)**: the area integral of the
winding number over a disk containing the image circle equals the shoelace contour
integral.  The hypothesis `1 < t` places the integration circle `‖w‖ = t` inside the
exterior `exteriorUnit = {1 < ‖w‖}`, where `extMap h` (and hence `deriv (extMap h)`) is
analytic — this is what makes the Fubini integrand jointly integrable.  The proof follows
the B1/B2/B3 route: unfold `winding`/`shoelace` to `θ`-integrals, swap the `p`- and
`θ`-integrals via `intervalIntegral_integral_swap` (joint integrability from a uniform
`1/‖·‖` bound on the disk, reusing the B1 machinery), apply `cauchyTransform_disk` to the
inner `p`-integral, and match the shoelace convention using `(2πi)⁻¹·π = (2i)⁻¹`. -/
theorem integral_winding_eq_shoelace (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {t R : ℝ} (ht : 1 < t)
    (hcurve : ∀ θ : ℝ, ‖extMap h (circleMap 0 t θ)‖ < R) :
    ∫ p in ball (0:ℂ) R, winding h t p = shoelace h t := by
  have htpos : 0 < t := lt_trans one_pos ht
  set G : ℂ → ℂ := extMap h with hGdef
  set G' : ℂ → ℂ := deriv (extMap h) with hG'def
  set f : ℝ → ℂ → ℂ := fun θ p =>
    (circleMap 0 t θ * I) * (G' (circleMap 0 t θ) / (G (circleMap 0 t θ) - p)) with hfdef
  -- winding unfolds to the θ-integral of f
  have hwind : ∀ p, winding h t p = (2 * ↑π * I)⁻¹ * ∫ θ in (0:ℝ)..2*π, f θ p := by
    intro p
    rw [winding]
    congr 1
    simp only [circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, smul_eq_mul, hfdef, hGdef, hG'def]
  -- joint integrability for Fubini
  have h_int : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc 0 (2*π))).prod (volume.restrict (ball (0:ℂ) R))) := by
    have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) (hcurve 0)
    have hmem : ∀ θ : ℝ, circleMap 0 t θ ∈ exteriorUnit := by
      intro θ
      simp only [exteriorUnit, mem_setOf_eq, norm_circleMap_zero, abs_of_pos htpos]
      exact ht
    have hGA : AnalyticOnNhd ℂ (extMap h) exteriorUnit := extMap_analyticOnNhd h hh
    have hGcont : Continuous (fun θ : ℝ => G (circleMap 0 t θ)) := by
      rw [hGdef]; exact hGA.continuousOn.comp_continuous (continuous_circleMap 0 t) hmem
    have hG'cont : Continuous (fun θ : ℝ => G' (circleMap 0 t θ)) := by
      rw [hG'def]; exact hGA.deriv.continuousOn.comp_continuous (continuous_circleMap 0 t) hmem
    have hmeasf : Measurable (Function.uncurry f) := by
      have m1 : Measurable (fun z : ℝ × ℂ => circleMap 0 t z.1 * I) :=
        (((continuous_circleMap 0 t).comp continuous_fst).mul continuous_const).measurable
      have m2 : Measurable (fun z : ℝ × ℂ => G' (circleMap 0 t z.1)) :=
        (hG'cont.comp continuous_fst).measurable
      have m3 : Measurable (fun z : ℝ × ℂ => G (circleMap 0 t z.1) - z.2) :=
        ((hGcont.comp continuous_fst).measurable).sub measurable_snd
      exact m1.mul (m2.div m3)
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2*π)).exists_bound_of_continuousOn
      hG'cont.continuousOn
    have hCfin : ∫⁻ q in ball (0:ℂ) (2*R), ‖q⁻¹‖ₑ < ⊤ := by
      have hib : IntegrableOn (fun q : ℂ => q⁻¹) (ball 0 (2*R)) volume := by
        refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_
        · show (1:ℕ) ≤ Module.finrank ℝ ℂ; rw [Complex.finrank_real_complex]; norm_num
        · show (1:ℝ) < (Module.finrank ℝ ℂ : ℝ); rw [Complex.finrank_real_complex]; norm_num
        · filter_upwards with x; rw [norm_inv, Real.rpow_neg_one, one_mul]
        · exact measurable_inv.aestronglyMeasurable
      have hf := hib.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at hf
      exact hf
    have hCbound : ∀ γ : ℂ, ‖γ‖ < R →
        ∫⁻ p in ball (0:ℂ) R, ‖(γ - p)⁻¹‖ₑ ≤ ∫⁻ q in ball (0:ℂ) (2*R), ‖q⁻¹‖ₑ := by
      intro γ hγ
      have hrefl : ∫⁻ p in ball (0:ℂ) R, ‖(γ - p)⁻¹‖ₑ = ∫⁻ p in ball (0:ℂ) R, ‖(p - γ)⁻¹‖ₑ := by
        apply setLIntegral_congr_fun measurableSet_ball
        intro p _
        show ‖(γ - p)⁻¹‖ₑ = ‖(p - γ)⁻¹‖ₑ
        rw [show γ - p = -(p - γ) from by ring, inv_neg, enorm_neg]
      rw [hrefl]
      have hmp : MeasurePreserving (fun p : ℂ => p - γ) volume volume :=
        measurePreserving_sub_right volume γ
      have hme : MeasurableEmbedding (fun p : ℂ => p - γ) :=
        (Homeomorph.subRight γ).measurableEmbedding
      rw [hmp.setLIntegral_comp_emb hme (fun q => ‖q⁻¹‖ₑ) (ball 0 R)]
      have himg : (fun p : ℂ => p - γ) '' ball 0 R = ball (-γ) R := by
        ext q; simp only [mem_image, mem_ball_iff_norm]
        constructor
        · rintro ⟨p, hp, rfl⟩; rw [sub_zero] at hp; rw [show p - γ - -γ = p from by ring]; exact hp
        · intro hq; refine ⟨q + γ, ?_, by ring⟩
          rw [sub_zero, show q + γ = q - -γ from by ring]; exact hq
      rw [himg]
      apply lintegral_mono_set
      apply ball_subset_ball'
      rw [dist_zero_right, norm_neg]; linarith
    refine ⟨hmeasf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, uIoc_of_le (by positivity : (0:ℝ) ≤ 2*π)]
    rw [lintegral_prod (fun z => ‖Function.uncurry f z‖ₑ) hmeasf.enorm.aemeasurable]
    calc ∫⁻ θ in Ioc (0:ℝ) (2*π), ∫⁻ p in ball (0:ℂ) R, ‖Function.uncurry f (θ, p)‖ₑ ∂volume ∂volume
        ≤ ∫⁻ _θ in Ioc (0:ℝ) (2*π),
            ENNReal.ofReal (t*M) * ∫⁻ q in ball (0:ℂ) (2*R), ‖q⁻¹‖ₑ ∂volume := by
          apply setLIntegral_mono measurable_const
          intro θ hθ
          have hθIcc : θ ∈ Icc (0:ℝ) (2*π) := ⟨le_of_lt hθ.1, hθ.2⟩
          have hfe : ∀ p : ℂ, ‖Function.uncurry f (θ, p)‖ₑ
              = ‖circleMap 0 t θ * I * G' (circleMap 0 t θ)‖ₑ * ‖(G (circleMap 0 t θ) - p)⁻¹‖ₑ := by
            intro p
            show ‖f θ p‖ₑ = _
            simp only [hfdef]
            rw [show (circleMap 0 t θ * I) * (G' (circleMap 0 t θ) / (G (circleMap 0 t θ) - p))
                = (circleMap 0 t θ * I * G' (circleMap 0 t θ)) * (G (circleMap 0 t θ) - p)⁻¹ from by
                  rw [div_eq_mul_inv]; ring, enorm_mul]
          simp_rw [hfe]
          have hmp2 : Measurable (fun p : ℂ => ‖(G (circleMap 0 t θ) - p)⁻¹‖ₑ) := by
            apply Measurable.enorm
            apply Measurable.inv
            exact measurable_const.sub measurable_id
          rw [lintegral_const_mul _ hmp2]
          apply mul_le_mul'
          · rw [← ofReal_norm]
            apply ENNReal.ofReal_le_ofReal
            rw [norm_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos htpos]
            exact mul_le_mul_of_nonneg_left (hM θ hθIcc) htpos.le
          · exact hCbound (G (circleMap 0 t θ)) (hcurve θ)
      _ = ENNReal.ofReal (t*M) * (∫⁻ q in ball (0:ℂ) (2*R), ‖q⁻¹‖ₑ) * volume (Ioc (0:ℝ) (2*π)) := by
          rw [setLIntegral_const]
      _ < ⊤ := by
          apply ENNReal.mul_lt_top
          · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCfin
          · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  -- scalar bookkeeping and assembly
  have hscalar : (2 * ↑π * I)⁻¹ * ↑π = (2 * I)⁻¹ := by
    have hpi : (↑π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    field_simp
  calc ∫ p in ball (0:ℂ) R, winding h t p
      = (2 * ↑π * I)⁻¹ * ∫ p in ball (0:ℂ) R, ∫ θ in (0:ℝ)..2*π, f θ p := by
        simp_rw [hwind]
        rw [MeasureTheory.integral_const_mul]
    _ = (2 * ↑π * I)⁻¹ * ∫ θ in (0:ℝ)..2*π, ∫ p in ball (0:ℂ) R, f θ p := by
        rw [(intervalIntegral_integral_swap h_int).symm]
    _ = (2 * ↑π * I)⁻¹ * ∫ θ in (0:ℝ)..2*π,
          (circleMap 0 t θ * I * G' (circleMap 0 t θ))
            * (↑π * (starRingEnd ℂ) (G (circleMap 0 t θ))) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro θ _
        show ∫ p in ball (0:ℂ) R, f θ p
            = (circleMap 0 t θ * I * G' (circleMap 0 t θ))
              * (↑π * (starRingEnd ℂ) (G (circleMap 0 t θ)))
        have hinner : ∫ p in ball (0:ℂ) R, f θ p
            = (circleMap 0 t θ * I * G' (circleMap 0 t θ))
              * ∫ p in ball (0:ℂ) R, (G (circleMap 0 t θ) - p)⁻¹ := by
          have hpt : ∀ p : ℂ, f θ p
              = (circleMap 0 t θ * I * G' (circleMap 0 t θ)) * (G (circleMap 0 t θ) - p)⁻¹ := by
            intro p; simp only [hfdef]; rw [div_eq_mul_inv]; ring
          simp_rw [hpt]
          rw [MeasureTheory.integral_const_mul]
        rw [hinner, cauchyTransform_disk (hcurve θ)]
    _ = (2 * ↑π * I)⁻¹ * (↑π * ∫ θ in (0:ℝ)..2*π,
          (circleMap 0 t θ * I) * ((starRingEnd ℂ) (G (circleMap 0 t θ)) * G' (circleMap 0 t θ))) := by
        congr 1
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro θ _
        ring
    _ = shoelace h t := by
        rw [shoelace, ← mul_assoc, hscalar]
        congr 1
        simp only [circleIntegral]
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [deriv_circleMap, smul_eq_mul, hGdef, hG'def]


/-! ## Laurent coefficient infrastructure (Stage C support) -/

section LaurentInfra

variable {h : ℂ → ℂ} {b : ℕ → ℂ}
  (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (h z))

include hb

/-- Coefficient boundedness: for `0 < r' < 1`, `‖b n‖ r'^n` is bounded. -/
theorem coeff_bdd {r' : ℝ} (hr'0 : 0 < r') (hr'1 : r' < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖b n‖ * r' ^ n ≤ C := by
  have hmem : (r' : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0]; exact hr'1
  have hsum := (hb (r' : ℂ) hmem).summable
  have htend : Tendsto (fun n => ‖b n * (r' : ℂ) ^ n‖) atTop (𝓝 0) := by
    have := hsum.tendsto_atTop_zero
    simpa using this.norm
  have hbdd : BddAbove (Set.range (fun n => ‖b n * (r' : ℂ) ^ n‖)) := htend.bddAbove_range
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  have hn : ‖b n * (r' : ℂ) ^ n‖ ≤ C := hC (Set.mem_range_self n)
  have heq : ‖b n * (r' : ℂ) ^ n‖ = ‖b n‖ * r' ^ n := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0]
  rw [heq] at hn
  exact le_trans hn (le_max_left _ _)

/-- Weighted coefficient summability: for `0 ≤ r < 1` and any `k`,
`∑ n^k ‖b n‖ r^n < ∞`. -/
theorem coeff_summable (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * ‖b n‖ * r ^ n) := by
  obtain ⟨r', hrr', hr'1⟩ := exists_between hr1
  have hr'0 : 0 < r' := lt_of_le_of_lt hr0 hrr'
  obtain ⟨C, hC0, hC⟩ := coeff_bdd hb hr'0 hr'1
  -- dominate by C * (n^k * (r/r')^n)
  have hq0 : 0 ≤ r / r' := div_nonneg hr0 hr'0.le
  have hq1 : r / r' < 1 := (div_lt_one hr'0).mpr hrr'
  have hqnorm : ‖(r / r' : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hgeo : Summable (fun n : ℕ => C * ((n : ℝ) ^ k * (r / r') ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one k hqnorm).mul_left C
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ k * ‖b n‖ * r ^ n := fun n =>
    mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (pow_nonneg hr0 n)
  have hle : ∀ n : ℕ, (n : ℝ) ^ k * ‖b n‖ * r ^ n ≤ C * ((n : ℝ) ^ k * (r / r') ^ n) := by
    intro n
    have hbn : ‖b n‖ * r' ^ n ≤ C := hC n
    have hrsplit : r ^ n = r' ^ n * (r / r') ^ n := by
      rw [div_pow, mul_comm, div_mul_cancel₀ _ (show (r' : ℝ) ^ n ≠ 0 by positivity)]
    calc (n : ℝ) ^ k * ‖b n‖ * r ^ n
        = (n : ℝ) ^ k * (r / r') ^ n * (‖b n‖ * r' ^ n) := by rw [hrsplit]; ring
      _ ≤ (n : ℝ) ^ k * (r / r') ^ n * C := by
          apply mul_le_mul_of_nonneg_left hbn (by positivity)
      _ = C * ((n : ℝ) ^ k * (r / r') ^ n) := by ring
  exact Summable.of_nonneg_of_le hnn hle hgeo

/-- Weighted squared-coefficient summability: for `0 ≤ r < 1` and any `k`,
`∑ n^k ‖b n‖² r^n < ∞`. -/
theorem coeff_sq_summable (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * ‖b n‖ ^ 2 * r ^ n) := by
  have hsr : Real.sqrt r < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt hr0 hr1
  obtain ⟨r', hsrr', hr'1⟩ := exists_between hsr
  have hr'0 : 0 < r' := lt_of_le_of_lt (Real.sqrt_nonneg r) hsrr'
  have hrr'2 : r < r' ^ 2 := by nlinarith [Real.sq_sqrt hr0, Real.sqrt_nonneg r, hsrr']
  obtain ⟨C, hC0, hC⟩ := coeff_bdd hb hr'0 hr'1
  have hq0 : 0 ≤ r / r' ^ 2 := div_nonneg hr0 (by positivity)
  have hq1 : r / r' ^ 2 < 1 := (div_lt_one (by positivity)).mpr hrr'2
  have hqnorm : ‖(r / r' ^ 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hgeo : Summable (fun n : ℕ => C ^ 2 * ((n : ℝ) ^ k * (r / r' ^ 2) ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one k hqnorm).mul_left (C ^ 2)
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ k * ‖b n‖ ^ 2 * r ^ n := fun n =>
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hr0 n)
  have hle : ∀ n : ℕ, (n : ℝ) ^ k * ‖b n‖ ^ 2 * r ^ n ≤ C ^ 2 * ((n : ℝ) ^ k * (r / r' ^ 2) ^ n) := by
    intro n
    have hbn : ‖b n‖ * r' ^ n ≤ C := hC n
    have hbn2 : ‖b n‖ ^ 2 * (r' ^ 2) ^ n ≤ C ^ 2 := by
      have hsq : (‖b n‖ * r' ^ n) ^ 2 ≤ C ^ 2 := by
        apply sq_le_sq'
        · linarith [mul_nonneg (norm_nonneg (b n)) (pow_nonneg hr'0.le n)]
        · exact hbn
      calc ‖b n‖ ^ 2 * (r' ^ 2) ^ n
          = (‖b n‖ * r' ^ n) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ C ^ 2 := hsq
    have hrsplit : r ^ n = (r' ^ 2) ^ n * (r / r' ^ 2) ^ n := by
      rw [div_pow, mul_comm, div_mul_cancel₀ _ (show ((r' : ℝ) ^ 2) ^ n ≠ 0 by positivity)]
    calc (n : ℝ) ^ k * ‖b n‖ ^ 2 * r ^ n
        = (n : ℝ) ^ k * (r / r' ^ 2) ^ n * (‖b n‖ ^ 2 * (r' ^ 2) ^ n) := by rw [hrsplit]; ring
      _ ≤ (n : ℝ) ^ k * (r / r' ^ 2) ^ n * C ^ 2 := by
          apply mul_le_mul_of_nonneg_left hbn2 (by positivity)
      _ = C ^ 2 * ((n : ℝ) ^ k * (r / r' ^ 2) ^ n) := by ring
  exact Summable.of_nonneg_of_le hnn hle hgeo

/-- Termwise derivative of the power series inside the unit ball. -/
theorem h_hasDerivAt {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasDerivAt h (∑' n : ℕ, (n : ℂ) * b n * z ^ (n - 1)) z := by
  rw [mem_ball_zero_iff] at hz
  obtain ⟨r', hzr', hr'1⟩ := exists_between hz
  have hr'0 : 0 < r' := lt_of_le_of_lt (norm_nonneg z) hzr'
  set g : ℕ → ℂ → ℂ := fun n y => b n * y ^ n with hgdef
  set g' : ℕ → ℂ → ℂ := fun n y => (n : ℂ) * b n * y ^ (n - 1) with hg'def
  set u : ℕ → ℝ := fun n => (1 / r') * ((n : ℝ) ^ 1 * ‖b n‖ * r' ^ n) with hudef
  have hu : Summable u := (coeff_summable hb 1 hr'0.le hr'1).mul_left (1 / r')
  have hg : ∀ n y, HasDerivAt (g n) (g' n y) y := by
    intro n y
    have hd := (hasDerivAt_pow n y).const_mul (b n)
    simp only [hgdef, hg'def]
    rw [show (n : ℂ) * b n * y ^ (n - 1) = b n * ((n : ℂ) * y ^ (n - 1)) from by ring]
    exact hd
  have hg'bound : ∀ n y, y ∈ ball (0 : ℂ) r' → ‖g' n y‖ ≤ u n := by
    intro n y hy
    rw [mem_ball_zero_iff] at hy
    have hyle : ‖y‖ ≤ r' := hy.le
    have hnorm : ‖g' n y‖ = (n : ℝ) * ‖b n‖ * ‖y‖ ^ (n - 1) := by
      simp only [hg'def, norm_mul, norm_pow, Complex.norm_natCast]
    rw [hnorm, hudef]
    have hpow : ‖y‖ ^ (n - 1) ≤ r' ^ (n - 1) :=
      pow_le_pow_left₀ (norm_nonneg y) hyle (n - 1)
    have hstep1 : (n : ℝ) * ‖b n‖ * ‖y‖ ^ (n - 1) ≤ (n : ℝ) * ‖b n‖ * r' ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    refine le_trans hstep1 ?_
    have hr'ne : r' ≠ 0 := ne_of_gt hr'0
    -- (n) ‖bn‖ r'^(n-1) ≤ (1/r')(n^1 ‖bn‖ r'^n)
    rcases n with _ | m
    · simp
    · have hrn : r' ^ (m + 1) = r' ^ m * r' := by rw [pow_succ]
      simp only [Nat.add_sub_cancel, pow_one]
      rw [hrn]
      apply le_of_eq
      field_simp
  have hg0 : Summable (fun n => g n (0 : ℂ)) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp only [hgdef]
    rw [zero_pow hn, mul_zero]
  have hkey := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball
    (convex_ball (0 : ℂ) r').isPreconnected (fun n y _ => hg n y) hg'bound
    (by rw [mem_ball_zero_iff, norm_zero]; exact hr'0)
    hg0 (show z ∈ ball (0 : ℂ) r' by rw [mem_ball_zero_iff]; exact hzr')
  -- transfer to h
  have hEq : h =ᶠ[𝓝 z] (fun y => ∑' n, g n y) := by
    have hnhd : ball (0 : ℂ) 1 ∈ 𝓝 z :=
      Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)
    filter_upwards [hnhd] with y hy
    exact ((hb y hy).tsum_eq).symm
  exact hkey.congr_of_eventuallyEq hEq

/-- Shifted coefficient summability. -/
theorem coeff_shift_summable {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ => ‖b (n + 1)‖ * s ^ (n + 1)) := by
  have h0 := coeff_summable hb 0 hs0 hs1
  simp only [pow_zero, one_mul] at h0
  exact (summable_nat_add_iff 1).mpr h0

/-- Shifted weighted coefficient summability (weight `n+2`). -/
theorem coeff_shift_summable2 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) * ‖b (n + 1)‖ * s ^ (n + 1)) := by
  have h1 := coeff_summable hb 1 hs0 hs1
  have h0 := coeff_summable hb 0 hs0 hs1
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖b n‖ * s ^ n) := by
    refine (h1.add h0).congr (fun n => ?_)
    simp only [pow_one, pow_zero, one_mul]; ring
  refine ((summable_nat_add_iff 1).mpr hsum).congr (fun n => ?_)
  push_cast; ring

/-- The exterior map's derivative on the exterior: `deriv (extMap h) w = 1 - h'(w⁻¹) w⁻²`. -/
theorem extMap_deriv_eq {w : ℂ} (hw : 1 < ‖w‖) :
    deriv (extMap h) w = 1 + deriv h w⁻¹ * (-(w ^ 2)⁻¹) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  have hwinv : w⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv, inv_lt_one_iff₀]; right; exact hw
  have hhD : HasDerivAt h (deriv h w⁻¹) w⁻¹ := (h_hasDerivAt hb hwinv).differentiableAt.hasDerivAt
  have hinvD : HasDerivAt (fun y : ℂ => y⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw0
  have hcomp : HasDerivAt (fun y => h y⁻¹) (deriv h w⁻¹ * (-(w ^ 2)⁻¹)) w := hhD.comp w hinvD
  have hid : HasDerivAt (fun y : ℂ => y) 1 w := hasDerivAt_id w
  exact (hid.add hcomp).deriv

/-- Tail representation on the ball: `h z - b 0 = ∑ₙ₌₁ bₙ zⁿ`. -/
theorem tail_hasSum_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n : ℕ => b (n + 1) * z ^ (n + 1)) (h z - b 0) := by
  have hb_z := hb z hz
  refine (hasSum_nat_add_iff (f := fun n => b n * z ^ n) 1).mpr ?_
  rw [Finset.sum_range_one]
  simp only [pow_zero, mul_one, sub_add_cancel]
  exact hb_z

/-- Summability of the derivative family at a point of the ball. -/
theorem deriv_family_summable {z : ℂ} (hz1 : ‖z‖ < 1) :
    Summable (fun n : ℕ => (n : ℂ) * b n * z ^ (n - 1)) := by
  obtain ⟨r', hzr', hr'1⟩ := exists_between hz1
  have hr'0 : 0 < r' := lt_of_le_of_lt (norm_nonneg z) hzr'
  have hu : Summable (fun n : ℕ => (1 / r') * ((n : ℝ) ^ 1 * ‖b n‖ * r' ^ n)) :=
    (coeff_summable hb 1 hr'0.le hr'1).mul_left _
  refine Summable.of_norm_bounded hu (fun n => ?_)
  have hnorm : ‖(n : ℂ) * b n * z ^ (n - 1)‖ = (n : ℝ) * ‖b n‖ * ‖z‖ ^ (n - 1) := by
    simp only [norm_mul, norm_pow, Complex.norm_natCast]
  rw [hnorm]
  have hpow : ‖z‖ ^ (n - 1) ≤ r' ^ (n - 1) :=
    pow_le_pow_left₀ (norm_nonneg z) hzr'.le (n - 1)
  have hstep1 : (n : ℝ) * ‖b n‖ * ‖z‖ ^ (n - 1) ≤ (n : ℝ) * ‖b n‖ * r' ^ (n - 1) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  refine le_trans hstep1 ?_
  have hr'ne : r' ≠ 0 := ne_of_gt hr'0
  rcases n with _ | m
  · simp
  · have hrn : r' ^ (m + 1) = r' ^ m * r' := by rw [pow_succ]
    simp only [Nat.add_sub_cancel, pow_one]
    rw [hrn]; apply le_of_eq; field_simp

/-- Numerator representation: `deriv h z · z + (h z − b 0) = ∑ₙ (n+2) b(n+1) z^(n+1)`. -/
theorem extMap_num_hasSum {z : ℂ} (hz1 : ‖z‖ < 1) (hzmem : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n : ℕ => ((n : ℂ) + 2) * b (n + 1) * z ^ (n + 1))
      (deriv h z * z + (h z - b 0)) := by
  -- derivative family HasSum
  have hs_d : HasSum (fun n : ℕ => (n : ℂ) * b n * z ^ (n - 1)) (deriv h z) := by
    rw [(h_hasDerivAt hb hzmem).deriv]
    exact (deriv_family_summable hb hz1).hasSum
  -- multiply by z and reindex
  have hs_dz : HasSum (fun n : ℕ => (n : ℂ) * b n * z ^ (n - 1) * z) (deriv h z * z) :=
    hs_d.mul_right z
  have hGeq : (fun m : ℕ => ((m : ℂ) + 1) * b (m + 1) * z ^ (m + 1))
      = (fun m : ℕ => ((m + 1 : ℕ) : ℂ) * b (m + 1) * z ^ ((m + 1) - 1) * z) := by
    funext m; simp only [Nat.add_sub_cancel]; push_cast; rw [pow_succ]; ring
  have hs_dz' : HasSum (fun m : ℕ => ((m : ℂ) + 1) * b (m + 1) * z ^ (m + 1)) (deriv h z * z) := by
    rw [hGeq]
    refine (hasSum_nat_add_iff (f := fun n => (n : ℂ) * b n * z ^ (n - 1) * z) 1).mpr ?_
    rw [Finset.sum_range_one]
    simpa using hs_dz
  -- tail HasSum
  have hs_tail0 : HasSum (fun n : ℕ => b (n + 1) * z ^ (n + 1)) (h z - b 0) :=
    tail_hasSum_ball hb hzmem
  -- add
  have hadd := hs_dz'.add hs_tail0
  have hfeq : (fun m : ℕ => ((m : ℂ) + 2) * b (m + 1) * z ^ (m + 1))
      = (fun m : ℕ => ((m : ℂ) + 1) * b (m + 1) * z ^ (m + 1) + b (m + 1) * z ^ (m + 1)) := by
    funext m; ring
  rw [hfeq]; exact hadd

/-- **hgrow bound** for A3/A4 at radius `t₁ > 1`, with `b0 = b 0`. -/
theorem extMap_grow_bound {t₁ : ℝ} (ht₁ : 1 < t₁) :
    ∀ w : ℂ, t₁ ≤ ‖w‖ → ‖extMap h w - w - b 0‖ ≤
      ∑' n : ℕ, ‖b (n + 1)‖ * (t₁⁻¹) ^ (n + 1) := by
  have ht₁0 : 0 < t₁ := by linarith
  have hs0 : 0 ≤ t₁⁻¹ := by positivity
  have hs1 : t₁⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; exact ht₁
  have hDsum := coeff_shift_summable hb hs0 hs1
  intro w hw
  have hw1 : 1 < ‖w‖ := lt_of_lt_of_le ht₁ hw
  have hbase : ‖w‖⁻¹ ≤ t₁⁻¹ := inv_anti₀ ht₁0 hw
  have hwinv : w⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv, inv_lt_one_iff₀]; right; exact hw1
  have htail := tail_hasSum_ball hb hwinv
  have heq : extMap h w - w - b 0 = h w⁻¹ - b 0 := by simp only [extMap]; ring
  have hbnd : ∀ n : ℕ, ‖b (n + 1) * (w⁻¹) ^ (n + 1)‖ ≤ ‖b (n + 1)‖ * (t₁⁻¹) ^ (n + 1) := by
    intro n; rw [norm_mul, norm_pow, norm_inv]; gcongr
  have hsn : Summable (fun n : ℕ => ‖b (n + 1) * (w⁻¹) ^ (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbnd hDsum
  rw [heq, htail.tsum_eq.symm]
  exact le_trans (norm_tsum_le_tsum_norm hsn) (Summable.tsum_le_tsum hbnd hsn hDsum)

/-- **hnum bound** for A3/A4 at radius `t₁ > 1`, with `b0 = b 0`. -/
theorem extMap_num_bound {t₁ : ℝ} (ht₁ : 1 < t₁) :
    ∀ w : ℂ, t₁ ≤ ‖w‖ → ‖w * deriv (extMap h) w - extMap h w + b 0‖ ≤
      ∑' n : ℕ, ((n : ℝ) + 2) * ‖b (n + 1)‖ * (t₁⁻¹) ^ (n + 1) := by
  have ht₁0 : 0 < t₁ := by linarith
  have hs0 : 0 ≤ t₁⁻¹ := by positivity
  have hs1 : t₁⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; exact ht₁
  have hD'sum := coeff_shift_summable2 hb hs0 hs1
  intro w hw
  have hw1 : 1 < ‖w‖ := lt_of_lt_of_le ht₁ hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1; linarith
  have hzmem : w⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv, inv_lt_one_iff₀]; right; exact hw1
  have hz1 : ‖w⁻¹‖ < 1 := by rw [norm_inv, inv_lt_one_iff₀]; right; exact hw1
  -- rewrite the numerator
  have hderiv := extMap_deriv_eq hb hw1
  have halg : w * deriv (extMap h) w - extMap h w + b 0
      = -(deriv h w⁻¹ * w⁻¹ + (h w⁻¹ - b 0)) := by
    rw [hderiv]
    simp only [extMap]
    field_simp
    ring
  rw [halg, norm_neg]
  have hbase : ‖w‖⁻¹ ≤ t₁⁻¹ := inv_anti₀ ht₁0 hw
  have hnum := extMap_num_hasSum hb hz1 hzmem
  have hbnd : ∀ n : ℕ, ‖((n : ℂ) + 2) * b (n + 1) * (w⁻¹) ^ (n + 1)‖
      ≤ ((n : ℝ) + 2) * ‖b (n + 1)‖ * (t₁⁻¹) ^ (n + 1) := by
    intro n
    rw [norm_mul, norm_mul, norm_pow, norm_inv]
    have hc : ‖(n : ℂ) + 2‖ = (n : ℝ) + 2 := by
      rw [show ((n : ℂ) + 2) = ((((n : ℝ) + 2 : ℝ)) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hc]; gcongr
  have hsn : Summable (fun n : ℕ => ‖((n : ℂ) + 2) * b (n + 1) * (w⁻¹) ^ (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbnd hD'sum
  rw [hnum.tsum_eq.symm]
  exact le_trans (norm_tsum_le_tsum_norm hsn) (Summable.tsum_le_tsum hbnd hsn hD'sum)

end LaurentInfra

end Uniformization
