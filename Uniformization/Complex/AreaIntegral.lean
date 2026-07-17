/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Complex.AreaWinding
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord

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
