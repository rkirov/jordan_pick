/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.Order
import Uniformization.RMT.RiemannMapping
import Uniformization.Complex.Bieberbach

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

open Set Metric Filter Topology

namespace Uniformization

/-- **Koebe growth theorem**: a schlicht function satisfies
`‖f z‖ ≤ ‖z‖ / (1 - ‖z‖)²` on the unit ball. -/
theorem koebe_growth {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  -- Bieberbach `‖a₂‖ ≤ 2` is now available (`Uniformization.bieberbach`), together with
  -- the coefficient helper `deriv_dslope_zero` (`a₂ = ½ H''(0)`).  What remains for this
  -- theorem is the classical distortion + double-integration argument, which is the largest
  -- analytic component of the Koebe chain and is NOT yet formalized:
  --   1. Apply `bieberbach` to the Koebe transform `T_w f` (schlicht on `ball 0 1`).
  --      Via `deriv_dslope_zero`, `a₂(T_w f) = ½ (f∘φ_w)''(0)` where `φ_w` is the disk
  --      automorphism `z ↦ (z+w)/(1+w̄ z)`.  The second-order chain rule gives
  --      `a₂(T_w f) = ½[(1-|w|²) f''(w)/f'(w) - 2 w̄]`, so `|…| ≤ 4`.
  --   2. `∂_r log|f'(re^{iθ})| = Re(e^{iθ} f''/f')` is bounded by `(2r+4)/(1-r²)`;
  --      radial FTC integration gives the distortion bound `|f'(z)| ≤ (1+r)/(1-r)³`.
  --   3. `f z = ∫₀¹ f'(tz)·z dt` integrates to `|f z| ≤ r/(1-r)²`.
  sorry

/-- **Koebe quarter theorem**: the image of a schlicht function contains the
ball of radius `1/4`. -/
theorem koebe_quarter {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1) :
    ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hballnhd : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds hmem0
  have hbf := bieberbach hf hinj h0 hd
  intro c hc
  rw [mem_ball_zero_iff] at hc
  by_cases hc0 : c = 0
  · exact ⟨0, hmem0, by rw [h0, hc0]⟩
  · by_contra hcni
    -- `c ∉ f '' ball 0 1`
    have hfc : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ c := by
      intro z hz hfz
      exact hcni ⟨z, hz, hfz⟩
    have hcfne : ∀ z ∈ ball (0 : ℂ) 1, c - f z ≠ 0 := by
      intro z hz
      exact sub_ne_zero.mpr (fun h => hfc z hz h.symm)
    set g : ℂ → ℂ := fun z => c * f z / (c - f z) with hgdef
    -- `g` differentiable
    have hg_diff : DifferentiableOn ℂ g (ball 0 1) := by
      rw [hgdef]
      exact ((differentiableOn_const c).mul hf).div
        ((differentiableOn_const c).sub hf) hcfne
    -- `g 0 = 0`
    have hg0 : g 0 = 0 := by simp [hgdef, h0]
    -- `deriv g 0 = 1`
    have hfderiv : HasDerivAt f 1 0 := by
      have := (hf.differentiableAt hballnhd).hasDerivAt
      rwa [hd] at this
    have hg_hasderiv : HasDerivAt g 1 0 := by
      have hnum : HasDerivAt (fun z => c * f z) (c * 1) 0 := hfderiv.const_mul c
      have hden : HasDerivAt (fun z => c - f z) (0 - 1) 0 :=
        (hasDerivAt_const 0 c).sub hfderiv
      have hden0 : (c - f 0) ≠ 0 := hcfne 0 hmem0
      have hval : (c * 1 * (c - f 0) - c * f 0 * (0 - 1)) / (c - f 0) ^ 2 = 1 := by
        rw [h0]; field_simp; ring
      have hq := hnum.div hden hden0
      rw [hval] at hq
      exact hq
    have hderiv_g0 : deriv g 0 = 1 := hg_hasderiv.deriv
    -- `g` injective
    have hg_inj : InjOn g (ball 0 1) := by
      intro a ha b hb hab
      simp only [hgdef] at hab
      have hda := hcfne a ha
      have hdb := hcfne b hb
      rw [div_eq_div_iff hda hdb] at hab
      -- hab : c * f a * (c - f b) = c * f b * (c - f a)
      have hcc : c * c ≠ 0 := mul_ne_zero hc0 hc0
      have hzero : c * c * (f a - f b) = 0 := by linear_combination hab
      have : f a = f b := by
        rcases mul_eq_zero.mp hzero with h | h
        · exact absurd h hcc
        · exact sub_eq_zero.mp h
      exact hinj ha hb this
    -- Bieberbach on `g`
    have hbg := bieberbach hg_diff hg_inj hg0 hderiv_g0
    -- `dslope g 0 = P` near 0 with `deriv P 0 = a₂(f) + 1/c`
    set P : ℂ → ℂ := fun z => c * dslope f 0 z / (c - f z) with hPdef
    have hEq : EqOn (dslope g 0) P (ball 0 1) := by
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0
        rw [dslope_same, hderiv_g0, hPdef]
        simp [dslope_same, hd, h0, hc0]
      · have hcfz := hcfne z hz
        rw [dslope_of_ne g hz0, slope_def_field, hg0, sub_zero, sub_zero]
        simp only [hgdef, hPdef, dslope_of_ne f hz0, slope_def_field, h0, sub_zero]
        field_simp
    have hEqev : dslope g 0 =ᶠ[𝓝 0] P := hEq.eventuallyEq_of_mem hballnhd
    have ha2g : deriv (dslope g 0) 0 = deriv (dslope f 0) 0 + 1 / c := by
      rw [hEqev.deriv_eq]
      -- deriv P 0
      have hu_hd : HasDerivAt (dslope f 0) (deriv (dslope f 0) 0) 0 := by
        have hv_diff : DifferentiableOn ℂ (dslope f 0) (ball 0 1) :=
          (Complex.differentiableOn_dslope hballnhd).mpr hf
        exact (hv_diff.differentiableAt hballnhd).hasDerivAt
      have hu0 : dslope f 0 0 = 1 := by rw [dslope_same, hd]
      have hnum : HasDerivAt (fun z => c * dslope f 0 z) (c * deriv (dslope f 0) 0) 0 :=
        hu_hd.const_mul c
      have hden : HasDerivAt (fun z => c - f z) (0 - 1) 0 :=
        (hasDerivAt_const 0 c).sub hfderiv
      have hden0 : (c - f 0) ≠ 0 := hcfne 0 hmem0
      have hP : HasDerivAt P
          ((c * deriv (dslope f 0) 0 * (c - f 0) - c * dslope f 0 0 * (0 - 1)) / (c - f 0) ^ 2) 0 := by
        rw [hPdef]; exact hnum.div hden hden0
      rw [hP.deriv, hu0, h0]
      field_simp [hc0]
      ring
    -- combine the two Bieberbach bounds
    rw [ha2g] at hbg
    have hkey : ‖(1 : ℂ) / c‖ ≤ 4 := by
      have h1 : ‖deriv (dslope f 0) 0 + 1 / c‖ ≤ 2 := hbg
      have h2 : ‖deriv (dslope f 0) 0‖ ≤ 2 := hbf
      have hid : (1 : ℂ) / c = (deriv (dslope f 0) 0 + 1 / c) - deriv (dslope f 0) 0 := by ring
      rw [hid]
      calc ‖(deriv (dslope f 0) 0 + 1 / c) - deriv (dslope f 0) 0‖
          ≤ ‖deriv (dslope f 0) 0 + 1 / c‖ + ‖deriv (dslope f 0) 0‖ := norm_sub_le _ _
        _ ≤ 4 := by linarith
    -- `‖1/c‖ = 1/‖c‖ ≥ 4` contradicts `‖c‖ < 1/4`
    rw [norm_div, norm_one] at hkey
    have hcnorm : 0 < ‖c‖ := by rw [norm_pos_iff]; exact hc0
    rw [div_le_iff₀ hcnorm] at hkey
    linarith

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
