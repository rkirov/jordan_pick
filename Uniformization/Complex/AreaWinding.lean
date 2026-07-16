/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Winding-number infrastructure for the area theorem (Stage A)

This file develops the winding-number layer that the Grönwall area theorem
(`Uniformization/Complex/AreaTheorem.lean`, lemma `groenwall_radius`) is built on,
following the route recorded there.  Working in exterior coordinates `w = 1/z`, the
univalent map `g z = z⁻¹ + h z` on the punctured unit ball becomes

  `extMap h w := w + h w⁻¹`  (`= g (w⁻¹)`),

holomorphic and injective on the exterior `{w | 1 < ‖w‖}`.  For a radius `t > 1` and
a point `p` the winding number of the image circle `extMap h '' {‖w‖ = t}` around `p`
is

  `winding h t p := (2πi)⁻¹ ∮_{|w|=t} (extMap h)'(w) / (extMap h w − p) dw`.

## What is proved here (sorry-free)

* `extMap_analyticOnNhd` : `extMap h` is analytic on `{1 < ‖w‖}`.
* `winding_eq_of_forall_ne` (**A1**) : the winding is constant across a zero-free
  closed annulus — i.e. if `extMap h w ≠ p` for all `w` with `s ≤ ‖w‖ ≤ t`, then
  `winding h t p = winding h s p`.  This is a direct application of the annulus
  Cauchy–Goursat theorem to the analytic integrand `(extMap h)'/(extMap h − p)`.

## Roadmap for the remaining stages (not yet formalized)

The remaining pieces needed to discharge `groenwall_radius`:

* **A2** (jump across a simple zero): if `extMap h w₀ = p` with `s < ‖w₀‖ < t` the
  unique zero in the closed annulus, then `winding h t p − winding h s p = 1`.
  Route: injectivity ⇒ `deriv (extMap h) w₀ ≠ 0`
  (copy `deriv_ne_zero_of_injOn` from `Uniformization/Surface/Injective.lean`);
  factor `extMap h − p = (w − w₀) • u` with `u` analytic non-vanishing near the
  annulus (`AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`, `n = 1`); split
  `(extMap h)'/(extMap h − p) = (w − w₀)⁻¹ + u'/u`; the `u'/u` part is equal on both
  circles by A1, the `(w − w₀)⁻¹` part gives `2πi` on the outer circle
  (`circleIntegral.integral_sub_inv_of_mem_ball`) and `0` on the inner circle.
* **A3** (value at infinity): for fixed `p`, `winding h t p = 1` for all large `t`
  (and for all `t > 1` when `p ∈ E_t`).  Route: with `b 0 = 0` (WLOG), the Laurent
  tail bounds give `(extMap h)'/(extMap h − p) − w⁻¹ = O(‖w‖⁻²)`, so the circle
  integral differs from `∮ w⁻¹ = 2πi` by `O(t⁻¹) → 0`; eventual constancy in `t`
  (A1, no zeros beyond the preimage's modulus) upgrades the limit to equality.
* **A4** (winding equals indicator): `winding h t p = 𝟙_{E_t}(p)` for a.e. `p`,
  where `E_t := (extMap h '' {‖w‖ > t})ᶜ`, by A1/A2/A3 case analysis + injectivity.
* **B** (integral identity): `∫_{p ∈ ball 0 R} winding h t p = shoelace h t` where
  `shoelace h t := (2i)⁻¹ ∮_{|w|=t} conj(extMap h w) · (extMap h)'(w) dw`, via Fubini
  and the Cauchy transform of the disk `∫_{ball 0 R} (ζ − p)⁻¹ = π conj ζ` (`‖ζ‖ ≤ R`).
* **C** (shoelace evaluation + finish): `shoelace h t = π(t² − ∑ n, n‖b n‖² t^{-2n})`
  by termwise circle integration (on `‖w‖ = t`, `conj w = t²/w`, reducing everything
  to `∮ wⁿ = 0` for `n ≠ -1`); then `0 ≤ vol(E_t) = ∫ winding = shoelace h t` gives
  `∑ n, n‖b n‖² t^{-2n} ≤ t²`, i.e. `groenwall_radius` after `ρ = 1/t`.
-/

open Set Metric Complex MeasureTheory

noncomputable section

namespace Uniformization

/-- The exterior form of the univalent map: `extMap h w = w + h w⁻¹ = g (w⁻¹)` where
`g z = z⁻¹ + h z`.  Holomorphic and injective on `{w | 1 < ‖w‖}`. -/
def extMap (h : ℂ → ℂ) : ℂ → ℂ := fun w => w + h w⁻¹

/-- The open exterior of the closed unit ball, `{w | 1 < ‖w‖}`. -/
def exteriorUnit : Set ℂ := {w : ℂ | 1 < ‖w‖}

/-- The exterior map is analytic on `{1 < ‖w‖}`. -/
theorem extMap_analyticOnNhd (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (ball 0 1)) :
    AnalyticOnNhd ℂ (extMap h) exteriorUnit := by
  have hinvA : AnalyticOnNhd ℂ (fun w : ℂ => w⁻¹) exteriorUnit := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0] at hw
      simp only [exteriorUnit, mem_setOf_eq, norm_zero] at hw; linarith
    exact analyticAt_inv hw0
  have hmaps : Set.MapsTo (fun w : ℂ => w⁻¹) exteriorUnit (ball 0 1) := by
    intro w hw
    simp only [exteriorUnit, mem_setOf_eq] at hw
    rw [mem_ball_zero_iff, norm_inv, inv_lt_one_iff₀]; right; exact hw
  exact analyticOnNhd_id.add (hh.comp hinvA hmaps)

/-- The winding number of the image circle `extMap h '' {‖w‖ = t}` around `p`:
`winding h t p = (2πi)⁻¹ ∮_{|w|=t} (extMap h)'(w) / (extMap h w − p) dw`. -/
def winding (h : ℂ → ℂ) (t : ℝ) (p : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(0, t), deriv (extMap h) w / (extMap h w - p)

/-- **A1**: the winding number is constant across a zero-free closed annulus.
If `extMap h w ≠ p` for every `w` with `s ≤ ‖w‖ ≤ t` (and `1 < s ≤ t`), then the
winding numbers at radii `t` and `s` agree. -/
theorem winding_eq_of_forall_ne (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) {p : ℂ}
    (hne : ∀ w : ℂ, s ≤ ‖w‖ → ‖w‖ ≤ t → extMap h w ≠ p) :
    winding h t p = winding h s p := by
  have hG := extMap_analyticOnNhd h hh
  have hG' : AnalyticOnNhd ℂ (deriv (extMap h)) exteriorUnit := hG.deriv
  set f : ℂ → ℂ := fun w => deriv (extMap h) w / (extMap h w - p) with hf
  -- `f` is analytic at every point of the closed annulus `s ≤ ‖w‖ ≤ t`.
  have hfA : ∀ z : ℂ, s ≤ ‖z‖ → ‖z‖ ≤ t → AnalyticAt ℂ f z := by
    intro z hz1 hz2
    have hzExt : z ∈ exteriorUnit := by
      simp only [exteriorUnit, mem_setOf_eq]; linarith
    have hden : extMap h z - p ≠ 0 := sub_ne_zero.mpr (hne z hz1 hz2)
    exact (hG' z hzExt).div ((hG z hzExt).sub analyticAt_const) hden
  -- membership bookkeeping for the closed annulus `closedBall 0 t \ ball 0 s`.
  have hcont : ContinuousOn f (closedBall (0 : ℂ) t \ ball (0 : ℂ) s) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [mem_closedBall_zero_iff] at hz1
    rw [mem_ball_zero_iff, not_lt] at hz2
    exact ((hfA z hz2 hz1).continuousAt).continuousWithinAt
  have hdiff : ∀ z ∈ (ball (0 : ℂ) t \ closedBall (0 : ℂ) s) \ (∅ : Set ℂ),
      DifferentiableAt ℂ f z := by
    intro z hz
    simp only [sdiff_empty] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [mem_ball_zero_iff] at hz1
    rw [mem_closedBall_zero_iff, not_le] at hz2
    exact (hfA z hz2.le hz1.le).differentiableAt
  have hkey := circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (by linarith : (0 : ℝ) < s) hst countable_empty hcont hdiff
  simp only [winding]
  rw [hkey]

end Uniformization
