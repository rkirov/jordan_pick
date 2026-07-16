/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.Order
import Uniformization.RMT.RiemannMapping

/-!
# Koebe growth and quarter theorems for univalent functions

For `f` injective and holomorphic on the unit ball with `f 0 = 0` and
`deriv f 0 = 1` (schlicht):

* `koebe_growth` : `‖f z‖ ≤ ‖z‖ / (1 - ‖z‖)²`;
* `koebe_quarter` : `ball 0 (1/4) ⊆ f '' ball 0 1`.

Route: Parseval on circles (area of image in terms of Taylor coefficients) ⇒
**area theorem** (`∑ n·‖b n‖² ≤ 1` for univalent `g(z) = 1/z + ∑ b n zⁿ` on the
punctured ball) ⇒ **Bieberbach** `‖a₂‖ ≤ 2` (apply the area theorem to
`1/√(f(z²))`, a branch supplied by `Complex.exists_branch_nthRoot` from the
ported RMT file) ⇒ growth/quarter by the standard Möbius-recentering argument.

These feed the parabolic case of the uniformization limit assembly: for
injective `g` on `ball 0 r` with `g 0 = 0`, `deriv g 0 = 1`, the scaled growth
bound `‖g w‖ ≤ ‖w‖ / (1 - ‖w‖/r)² ≤ 4‖w‖` for `‖w‖ ≤ r/2` gives the local
uniform boundedness that Montel needs.
-/

open Set Metric

namespace Uniformization

/-- **Koebe growth theorem**: a schlicht function satisfies
`‖f z‖ ≤ ‖z‖ / (1 - ‖z‖)²` on the unit ball. -/
theorem koebe_growth {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  -- BLOCKED on the area theorem / Bieberbach `‖a₂‖ ≤ 2`.  Route once Bieberbach is
  -- available: apply it to the Koebe transform of `f` at `w`, giving
  -- `|(1-|w|²) f''(w)/f'(w) - 2 w̄| ≤ 4`; integrate the resulting bound on
  -- `∂_r log|f'|` radially (distortion `|f'| ≤ (1+|w|)/(1-|w|)³`), then integrate
  -- once more radially for the growth bound.  See report for the area-theorem status.
  sorry

/-- **Koebe quarter theorem**: the image of a schlicht function contains the
ball of radius `1/4`. -/
theorem koebe_quarter {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1) :
    ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  -- BLOCKED on the area theorem / Bieberbach `‖a₂‖ ≤ 2`.  Route once Bieberbach is
  -- available: if `c ∉ f '' ball 0 1` then `h := f/(1 - f/c)` is schlicht with second
  -- coefficient `a₂ + 1/c`; Bieberbach on `h` and `f` give `‖1/c‖ ≤ 4`, i.e. `‖c‖ ≥ 1/4`.
  sorry

/-- Scaled growth bound on `ball 0 r`, in the convenient form for the
uniformization limit assembly: `‖g w‖ ≤ 4‖w‖` on the half-radius ball. -/
theorem norm_le_four_mul_norm_of_injOn {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 r)) (hinj : InjOn g (ball 0 r))
    (h0 : g 0 = 0) (hd : deriv g 0 = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (r / 2)) :
    ‖g w‖ ≤ 4 * ‖w‖ := by
  -- Rescale to the unit ball: `f z := g (r z) / r` is schlicht on `ball 0 1`.
  set R : ℂ := (r : ℂ) with hR
  have hR0 : R ≠ 0 := by simp [hR, ne_of_gt hr]
  have hRnorm : ‖R‖ = r := by simp [hR, abs_of_pos hr]
  -- The linear map `z ↦ R z` maps `ball 0 1` into `ball 0 r`.
  have hmaps : ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → R * z ∈ ball (0 : ℂ) r := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul, hRnorm]
    calc r * ‖z‖ < r * 1 := by exact mul_lt_mul_of_pos_left hz hr
      _ = r := mul_one r
  set f : ℂ → ℂ := fun z => g (R * z) / R with hf
  -- `f` is differentiable on `ball 0 1`.
  have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
    apply DifferentiableOn.div_const
    apply DifferentiableOn.comp (t := ball 0 r) hg
    · exact (differentiable_id.const_mul R).differentiableOn
    · intro z hz; exact hmaps hz
  -- `f` is injective on `ball 0 1`.
  have hfinj : InjOn f (ball 0 1) := by
    intro z₁ hz₁ z₂ hz₂ h
    simp only [hf] at h
    have : g (R * z₁) = g (R * z₂) := by
      field_simp at h; exact h
    have := hinj (hmaps hz₁) (hmaps hz₂) this
    exact mul_left_cancel₀ hR0 this
  -- `f 0 = 0`.
  have hf0 : f 0 = 0 := by simp [hf, h0]
  -- `deriv f 0 = 1`.
  have hg0 : HasDerivAt g 1 0 := by
    have hda : DifferentiableAt ℂ g 0 :=
      hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    rw [← hd]; exact hda.hasDerivAt
  have hfderiv : HasDerivAt f 1 0 := by
    have h1 : HasDerivAt (fun z : ℂ => R * z) R 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul R
    have hg0' : HasDerivAt g 1 (R * 0) := by simpa using hg0
    have h2 : HasDerivAt (fun z : ℂ => g (R * z)) (1 * R) 0 := hg0'.comp 0 h1
    have h3 : HasDerivAt f (1 * R / R) 0 := h2.div_const R
    have : (1 : ℂ) * R / R = 1 := by field_simp
    rw [this] at h3
    exact h3
  have hfd : deriv f 0 = 1 := hfderiv.deriv
  -- Apply the sharp Koebe growth bound to `f` at `z := w / R`.
  set z : ℂ := w / R with hz
  have hznorm : ‖z‖ = ‖w‖ / r := by rw [hz, norm_div, hRnorm]
  have hwlt : ‖w‖ < r / 2 := by rwa [mem_ball_zero_iff] at hw
  have hzlt : ‖z‖ < 1 / 2 := by
    rw [hznorm]
    rw [div_lt_div_iff₀ hr (by norm_num)]
    linarith
  have hzmem : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hznorm]
    have : ‖w‖ / r < 1 / 2 := by rw [← hznorm]; exact hzlt
    linarith
  have hgrow := koebe_growth hfdiff hfinj hf0 hfd hzmem
  -- Translate `f z = g w / R`.
  have hRzw : R * z = w := by rw [hz]; field_simp
  have hfz : f z = g w / R := by show g (R * z) / R = g w / R; rw [hRzw]
  rw [hfz, norm_div, hRnorm] at hgrow
  -- `‖g w‖ / r ≤ ‖z‖ / (1 - ‖z‖)²`, and `1/(1-‖z‖)² ≤ 4` since `‖z‖ ≤ 1/2`.
  rw [hznorm] at hgrow
  have hpos : (0 : ℝ) < 1 - ‖w‖ / r := by
    have : ‖w‖ / r < 1 / 2 := by rw [← hznorm]; exact hzlt
    linarith
  have hgw : ‖g w‖ ≤ ‖w‖ / (1 - ‖w‖ / r) ^ 2 := by
    rw [div_le_iff₀ hr] at hgrow
    calc ‖g w‖ ≤ (‖w‖ / r) / (1 - ‖w‖ / r) ^ 2 * r := hgrow
      _ = ‖w‖ / (1 - ‖w‖ / r) ^ 2 := by field_simp
  have hbound : ‖w‖ / (1 - ‖w‖ / r) ^ 2 ≤ 4 * ‖w‖ := by
    rw [div_le_iff₀ (by positivity)]
    have hhalf : ‖w‖ / r ≤ 1 / 2 := by
      have : ‖w‖ / r < 1 / 2 := by rw [← hznorm]; exact hzlt
      linarith
    have ht : (1 : ℝ) / 2 ≤ 1 - ‖w‖ / r := by linarith
    have hs : (1 - ‖w‖ / r) ^ 2 ≥ 1 / 4 := by nlinarith [ht]
    nlinarith [mul_nonneg (norm_nonneg w) (by linarith [hs] : (0:ℝ) ≤ 4 * (1 - ‖w‖ / r) ^ 2 - 1)]
  linarith [hgw, hbound]

end Uniformization
