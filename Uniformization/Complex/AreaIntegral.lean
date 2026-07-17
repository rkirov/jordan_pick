/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Complex.AreaWinding
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

Proved sorry-free here: the shoelace definition and **both angular halves of B1** —
`angular_lt` (`∫₀^{2π} (ζ − r e^{iθ})⁻¹ dθ = 2π/ζ` for `|r| < ‖ζ‖`, mean value, via
`circleAverage_of_differentiable_on_off_countable`) and `angular_gt` (`= 0` for
`‖ζ‖ < r`, via partial fractions on the circle).

The main identity `integral_winding_eq_shoelace` is the single `sorry`.  The remaining
work to close it, now that both angular integrals are in hand:
* `cauchyTransform_disk` (B1): `∫_{p ∈ ball 0 R} (ζ − p)⁻¹ = π · conj ζ` for `‖ζ‖ < R`.
  Route: `IntegrableOn (ζ − ·)⁻¹ (ball 0 R)` (measure-preserving reflection
  `p ↦ ζ − p` sends `ball 0 R` to `ball ζ R ⊆ ball 0 (‖ζ‖+R)`, then
  `integrableOn_ball_of_norm_le_rpow` with `α = 1 < 2 = finrank ℝ ℂ`); polar change of
  variables `Complex.integral_comp_polarCoord_symm` (with `ball 0 R` indicator);
  `setIntegral_prod` to iterate; `Function.Periodic.intervalIntegral_add_eq` to move the
  angular integral from `(−π,π)` to `(0,2π)` and apply `angular_lt`/`angular_gt`;
  radial split at `‖ζ‖` (`integral_add_adjacent_intervals`) and `∫₀^{‖ζ‖} (2π/ζ)·r dr
  = π‖ζ‖²/ζ = π·conj ζ`.
* B2/B3 (Fubini + assembly): `integral_integral_swap` on the winding integrand (jointly
  integrable via the same `1/‖·‖` local integrability), then apply `cauchyTransform_disk`
  and match the shoelace convention (`(2πi)⁻¹·π = (2i)⁻¹`).
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
integral.  See the module docstring for the full B1/B2/B3 route; the remaining
measure-theory assembly (Cauchy transform of the disk + Fubini) is the single
`sorry`. -/
theorem integral_winding_eq_shoelace (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {t R : ℝ} (ht : 0 < t)
    (hcurve : ∀ θ : ℝ, ‖extMap h (circleMap 0 t θ)‖ < R) :
    ∫ p in ball (0:ℂ) R, winding h t p = shoelace h t := by
  sorry

end Uniformization
