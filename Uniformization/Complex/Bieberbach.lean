/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Uniformization.Complex.AreaTheorem

/-!
# Bieberbach's `‖a₂‖ ≤ 2` for schlicht functions
-/

open Set Metric Complex Filter Topology

namespace Uniformization

/-- An analytic square root of a nonvanishing analytic function on the unit ball,
normalized to value `1` at `0`. -/
theorem exists_sqrt {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v (ball 0 1))
    (hv0 : ∀ z ∈ ball (0 : ℂ) 1, v z ≠ 0) (hv1 : v 0 = 1) :
    ∃ T : ℂ → ℂ, DifferentiableOn ℂ T (ball 0 1) ∧ T 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, T z ^ 2 = v z) ∧ (∀ z ∈ ball (0 : ℂ) 1, T z ≠ 0) := by
  have hvan : AnalyticOnNhd ℂ v (ball 0 1) := hv.analyticOnNhd isOpen_ball
  -- logarithmic derivative is analytic hence differentiable on the ball
  have hlog : DifferentiableOn ℂ (logDeriv v) (ball 0 1) :=
    (hvan.deriv.div hvan hv0).differentiableOn
  -- a primitive `L` with `L 0 = 0`
  obtain ⟨L, hL0, hL⟩ := hlog.isExactOn_ball.with_val_at 0 0
  refine ⟨fun z => Complex.exp (L z / 2), ?_, ?_, ?_, ?_⟩
  · -- differentiable
    intro z hz
    have hLz : HasDerivAt L (logDeriv v z) z := hL z hz
    have : HasDerivAt (fun z => Complex.exp (L z / 2))
        (Complex.exp (L z / 2) * (logDeriv v z / 2)) z :=
      ((hLz.div_const 2).cexp)
    exact this.differentiableAt.differentiableWithinAt
  · simp [hL0]
  · -- `T z ^ 2 = v z`
    -- first prove `v z = exp (L z)` via a constant-ratio argument
    have hveq : ∀ z ∈ ball (0 : ℂ) 1, v z = Complex.exp (L z) := by
      set W : ℂ → ℂ := fun z => v z * Complex.exp (- L z) with hWdef
      have hWderiv : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt W 0 z := by
        intro z hz
        have hvz : HasDerivAt v (deriv v z) z :=
          (hv.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
        have hLz : HasDerivAt L (logDeriv v z) z := hL z hz
        have hexp : HasDerivAt (fun z => Complex.exp (- L z))
            (Complex.exp (- L z) * (- logDeriv v z)) z := by
          have := (hLz.neg).cexp
          simpa using this
        have hprod := hvz.mul hexp
        have hvz0 : v z ≠ 0 := hv0 z hz
        have hval : deriv v z * Complex.exp (-L z)
            + v z * (Complex.exp (-L z) * (-logDeriv v z)) = 0 := by
          have hld : logDeriv v z = deriv v z / v z := rfl
          rw [hld]; field_simp; ring
        rw [hval] at hprod
        exact hprod
      have hWdiff : DifferentiableOn ℂ W (ball 0 1) :=
        fun z hz => (hWderiv z hz).differentiableAt.differentiableWithinAt
      have hWfd : ∀ x ∈ ball (0 : ℂ) 1, fderivWithin ℂ W (ball 0 1) x = 0 := by
        intro x hx
        rw [fderivWithin_of_isOpen isOpen_ball hx, (hWderiv x hx).hasFDerivAt.fderiv]
        ext1; simp
      intro z hz
      have hconst : W z = W 0 :=
        (convex_ball 0 1).is_const_of_fderivWithin_eq_zero hWdiff hWfd hz (mem_ball_self one_pos)
      have hW0 : W 0 = 1 := by simp [hWdef, hv1, hL0]
      rw [hW0] at hconst
      -- `v z * exp (-L z) = 1 ⇒ v z = exp (L z)`
      have hexpne : Complex.exp (- L z) ≠ 0 := Complex.exp_ne_zero _
      have hmul : v z * Complex.exp (- L z) = 1 := hconst
      have hkey : v z = (Complex.exp (- L z))⁻¹ := by
        field_simp; linear_combination hmul
      rw [hkey, Complex.exp_neg, inv_inv]
    intro z hz
    rw [show (Complex.exp (L z / 2)) ^ 2 = Complex.exp (L z / 2) * Complex.exp (L z / 2) from by ring,
      ← Complex.exp_add]
    rw [show L z / 2 + L z / 2 = L z from by ring, ← hveq z hz]
  · intro z hz; exact Complex.exp_ne_zero _

/-- **Bieberbach's inequality** for a schlicht function `f` on the unit ball:
the second Taylor coefficient `a₂ = deriv (dslope f 0) 0` satisfies `‖a₂‖ ≤ 2`. -/
theorem bieberbach {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1) :
    ‖deriv (dslope f 0) 0‖ ≤ 2 := by
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hballnhd : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds hmem0
  have hsq : ∀ z ∈ ball (0 : ℂ) 1, z ^ 2 ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hsqmap : MapsTo (fun z : ℂ => z ^ 2) (ball 0 1) (ball 0 1) := fun z hz => hsq z hz
  have hsq_diff : DifferentiableOn ℂ (fun z : ℂ => z ^ 2) (ball 0 1) :=
    (differentiable_pow 2).differentiableOn
  -- factorization `f = id * v`, `v = dslope f 0`
  set v : ℂ → ℂ := dslope f 0 with hvdef
  have hv_diff : DifferentiableOn ℂ v (ball 0 1) :=
    (Complex.differentiableOn_dslope hballnhd).mpr hf
  have hv0 : v 0 = 1 := by rw [hvdef, dslope_same, hd]
  have hfv : ∀ w : ℂ, w * v w = f w := by
    intro w
    have := sub_smul_dslope f 0 w
    simpa [hvdef, h0, smul_eq_mul] using this
  have hv_ne : ∀ z ∈ ball (0 : ℂ) 1, v z ≠ 0 := by
    intro z hz hvz
    have hfz : f z = 0 := by rw [← hfv z, hvz, mul_zero]
    have : z = 0 := hinj hz hmem0 (by rw [hfz, h0])
    rw [this] at hvz; rw [hv0] at hvz; exact one_ne_zero hvz
  -- analytic square root `T` with `T ^ 2 = v`
  obtain ⟨T, hT_diff, hT0, hT_sq, hT_ne⟩ := exists_sqrt hv_diff hv_ne hv0
  have hT2_diff : DifferentiableOn ℂ (fun z : ℂ => T (z ^ 2)) (ball 0 1) :=
    hT_diff.comp hsq_diff hsqmap
  have hT2_ne : ∀ z ∈ ball (0 : ℂ) 1, T (z ^ 2) ≠ 0 := fun z hz => hT_ne _ (hsq z hz)
  -- the odd square-root transform `G₁ z = z * T (z ^ 2)`
  set G₁ : ℂ → ℂ := fun z => z * T (z ^ 2) with hG₁def
  have hG₁_sq : ∀ z ∈ ball (0 : ℂ) 1, G₁ z ^ 2 = f (z ^ 2) := by
    intro z hz
    have h1 : T (z ^ 2) ^ 2 = v (z ^ 2) := hT_sq _ (hsq z hz)
    rw [hG₁def]
    rw [mul_pow, h1, ← hfv (z ^ 2)]
  have hG₁_ne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → G₁ z ≠ 0 := by
    intro z hz hz0
    rw [hG₁def]
    exact mul_ne_zero hz0 (hT2_ne z hz)
  have hG₁_inj : InjOn G₁ (ball 0 1) := by
    intro a ha b hb hab
    have hsqeq : f (a ^ 2) = f (b ^ 2) := by
      rw [← hG₁_sq a ha, ← hG₁_sq b hb, hab]
    have habsq : a ^ 2 = b ^ 2 := hinj (hsq a ha) (hsq b hb) hsqeq
    have hfac : (a - b) * (a + b) = 0 := by ring_nf; linear_combination habsq
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact sub_eq_zero.mp h1
    · -- a = -b, force both zero
      have hab' : a = -b := by linear_combination h2
      have hGa : G₁ a = - G₁ b := by
        rw [hab']; simp only [hG₁def]
        rw [show (-b) ^ 2 = b ^ 2 from by ring]; ring
      rw [hab] at hGa
      have hGb0 : G₁ b = 0 := by linear_combination hGa / 2
      have hb0 : b = 0 := by by_contra hb0; exact hG₁_ne b hb hb0 hGb0
      have ha0 : a = 0 := by rw [hab', hb0, neg_zero]
      rw [ha0, hb0]
  -- the exterior transform `h z = z⁻¹ + h z = 1 / G₁ z` in interior coordinates
  set R : ℂ → ℂ := fun z => (-(dslope T 0 (z ^ 2))) / T (z ^ 2) with hRdef
  set hh : ℂ → ℂ := fun z => z * R z with hhdef
  have hdsl_diff : DifferentiableOn ℂ (dslope T 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope hballnhd).mpr hT_diff
  have hdsl2_diff : DifferentiableOn ℂ (fun z : ℂ => dslope T 0 (z ^ 2)) (ball 0 1) :=
    hdsl_diff.comp hsq_diff hsqmap
  have hR_diff : DifferentiableOn ℂ R (ball 0 1) := by
    rw [hRdef]
    exact (hdsl2_diff.neg).div hT2_diff hT2_ne
  have hh_diff : DifferentiableOn ℂ hh (ball 0 1) := by
    rw [hhdef]
    exact differentiableOn_id.mul hR_diff
  have hh_an : AnalyticOnNhd ℂ hh (ball 0 1) := hh_diff.analyticOnNhd isOpen_ball
  -- reciprocal identity `z⁻¹ + hh z = (G₁ z)⁻¹` on the punctured ball
  have hrecip : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → z⁻¹ + hh z = (G₁ z)⁻¹ := by
    intro z hz hz0
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
    have hTz2 : T (z ^ 2) ≠ 0 := hT2_ne z hz
    have hds : dslope T 0 (z ^ 2) = (T (z ^ 2) - 1) / z ^ 2 := by
      rw [dslope_of_ne T hz2, slope_def_field, hT0, sub_zero]
    rw [hhdef, hRdef, hG₁def]
    simp only [hds]
    field_simp
    ring
  -- injectivity of `z⁻¹ + hh` on the punctured ball
  have hφinj : InjOn (fun z => z⁻¹ + hh z) (ball 0 1 \ {0}) := by
    intro a ha b hb hab
    obtain ⟨haball, ha0⟩ := ha
    obtain ⟨hbball, hb0⟩ := hb
    rw [mem_singleton_iff] at ha0 hb0
    have hra := hrecip a haball ha0
    have hrb := hrecip b hbball hb0
    have : (G₁ a)⁻¹ = (G₁ b)⁻¹ := by rw [← hra, ← hrb]; exact hab
    have hGeq : G₁ a = G₁ b := inv_inj.mp this
    exact hG₁_inj haball hbball hGeq
  -- Taylor coefficients of `hh`
  set b : ℕ → ℂ := fun n => (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n hh 0 with hbdef
  have hb : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (hh z) := by
    intro z hz
    have hts := Complex.hasSum_taylorSeries_on_ball hh_diff hz
    have heq : (fun n => b n * z ^ n)
        = (fun n : ℕ => (Nat.factorial n : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n hh 0) := by
      funext n; rw [hbdef]; simp only [smul_eq_mul, sub_zero]; ring
    rw [heq]; exact hts
  have hb1 : b 1 = deriv hh 0 := by
    rw [hbdef]; simp [iteratedDeriv_one, Nat.factorial_one]
  -- apply the area theorem at `N = 1`
  have harea := area_theorem hh_an hb hφinj 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_add, zero_mul, one_mul] at harea
  -- `∑_{n<2} n ‖b n‖² = ‖b 1‖²`
  have hb1_le : ‖b 1‖ ^ 2 ≤ 1 := harea
  have hb1_norm : ‖deriv hh 0‖ ≤ 1 := by
    rw [← hb1]
    nlinarith [norm_nonneg (b 1), hb1_le]
  -- relate `deriv v 0` and `deriv hh 0`
  have hT0d : HasDerivAt T (deriv T 0) 0 :=
    (hT_diff.differentiableAt hballnhd).hasDerivAt
  -- `deriv hh 0 = R 0 = - deriv T 0`
  have hR0 : R 0 = - deriv T 0 := by
    rw [hRdef]; simp [dslope_same, hT0]
  have hderiv_hh0 : deriv hh 0 = - deriv T 0 := by
    have hRd : HasDerivAt R (deriv R 0) 0 :=
      (hR_diff.differentiableAt hballnhd).hasDerivAt
    have : HasDerivAt hh (1 * R 0 + 0 * deriv R 0) 0 := by
      rw [hhdef]; exact (hasDerivAt_id (0 : ℂ)).mul hRd
    rw [this.deriv]; simp [hR0]
  -- `deriv v 0 = 2 * deriv T 0`
  have hveqT : v =ᶠ[𝓝 0] fun z => T z ^ 2 := by
    filter_upwards [hballnhd] with z hz using (hT_sq z hz).symm
  have hderiv_v0 : deriv v 0 = 2 * deriv T 0 := by
    rw [hveqT.deriv_eq]
    have : HasDerivAt (fun z => T z ^ 2) (2 * T 0 ^ (2 - 1) * deriv T 0) 0 := hT0d.pow 2
    rw [this.deriv]; simp [hT0]
  -- conclude
  have : deriv v 0 = -2 * deriv hh 0 := by rw [hderiv_v0, hderiv_hh0]; ring
  rw [hvdef] at this ⊢
  rw [this, norm_mul]
  simp only [norm_neg]
  rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
  nlinarith [hb1_norm, norm_nonneg (deriv (dslope f 0) 0)]

/-- For `H` analytic on a neighbourhood of `0`, the first Taylor coefficient of
`dslope H 0` equals half the second derivative of `H`.  (Support for the Koebe
distortion computation: `a₂(H) = deriv (dslope H 0) 0 = ½ H''(0)`.) -/
theorem deriv_dslope_zero {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hU0 : (0 : ℂ) ∈ U)
    (hH : DifferentiableOn ℂ H U) :
    deriv (deriv H) 0 = 2 * deriv (dslope H 0) 0 := by
  set D : ℂ → ℂ := dslope H 0 with hDdef
  have hUnhd : U ∈ 𝓝 (0 : ℂ) := hU.mem_nhds hU0
  have hD_diff : DifferentiableOn ℂ D U :=
    (Complex.differentiableOn_dslope hUnhd).mpr hH
  have hDan : AnalyticOnNhd ℂ D U := hD_diff.analyticOnNhd hU
  -- `H z = H 0 + z * D z` everywhere
  have hHfac : ∀ z, H z = H 0 + z * D z := by
    intro z
    have h := sub_smul_dslope H 0 z
    simp only [sub_zero, smul_eq_mul] at h
    rw [hDdef]; linear_combination -h
  -- `deriv H =ᶠ[𝓝 0] fun z => D z + z * deriv D z`
  have hderivH : deriv H =ᶠ[𝓝 0] fun z => D z + z * deriv D z := by
    filter_upwards [hUnhd] with z hz
    have hDz : HasDerivAt D (deriv D z) z :=
      (hD_diff.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hHz : HasDerivAt H (D z + z * deriv D z) z := by
      have hstep : HasDerivAt (fun z => H 0 + z * D z)
          (0 + (1 * D z + z * deriv D z)) z :=
        (hasDerivAt_const z (H 0)).add ((hasDerivAt_id z).mul hDz)
      have heq : (0 : ℂ) + (1 * D z + z * deriv D z) = D z + z * deriv D z := by ring
      rw [heq] at hstep
      exact hstep.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => hHfac y))
    exact hHz.deriv
  -- differentiate once more at 0
  have hderivD0 : HasDerivAt (deriv D) (deriv (deriv D) 0) 0 :=
    (hDan.deriv.differentiableOn.differentiableAt hUnhd).hasDerivAt
  have hD0 : HasDerivAt D (deriv D 0) 0 :=
    (hD_diff.differentiableAt hUnhd).hasDerivAt
  have hsecond : HasDerivAt (fun z => D z + z * deriv D z)
      (deriv D 0 + (1 * deriv D 0 + 0 * deriv (deriv D) 0)) 0 :=
    hD0.add ((hasDerivAt_id (0 : ℂ)).mul hderivD0)
  rw [hderivH.deriv_eq, hsecond.deriv]
  ring

end Uniformization
