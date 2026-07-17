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

Proved sorry-free here: the shoelace definition and **`angular_lt`**, the mean-value
core of B1 (`∫₀^{2π} (ζ − r e^{iθ})⁻¹ dθ = 2π/ζ` for `|r| < ‖ζ‖`, via the pin's
`circleAverage_of_differentiable_on_off_countable`).

The main identity `integral_winding_eq_shoelace` is the single `sorry`: it still needs
`angular_gt`, the polar radial assembly (B1), and the singular-kernel Fubini (B2/B3).
These are substantial measure-theory steps (change of variables to polar over a ball,
`Complex.integral_comp_polarCoord_symm`; joint integrability of a `1/‖·‖`-type kernel;
`integral_integral_swap`) left for a follow-up.
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
