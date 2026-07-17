import Uniformization.Complex.AreaIntegral

open Set Metric Complex MeasureTheory Topology Filter Real intervalIntegral

noncomputable section

namespace Uniformization

variable {h : ℂ → ℂ} {b : ℕ → ℂ}

/-- Interchange of `∮` and a series with a summable uniform bound on the circle
(via dominated convergence for interval integrals). -/
private lemma hasSum_circleIntegral_of_bound {t : ℝ} (ht : 0 < t) (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (u : ℕ → ℝ) (hu : Summable u)
    (hcont : ∀ k, ContinuousOn (f k) (sphere (0 : ℂ) t))
    (hbound : ∀ k, ∀ w ∈ sphere (0 : ℂ) t, ‖f k w‖ ≤ u k)
    (hgsum : ∀ w ∈ sphere (0 : ℂ) t, HasSum (fun k => f k w) (g w)) :
    HasSum (fun k => ∮ w in C(0, t), f k w) (∮ w in C(0, t), g w) := by
  have hmem : ∀ θ : ℝ, circleMap 0 t θ ∈ sphere (0 : ℂ) t :=
    fun θ => circleMap_mem_sphere 0 ht.le θ
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => t * u k) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hc : Continuous fun θ : ℝ => f k (circleMap 0 t θ) :=
      (hcont k).comp_continuous (continuous_circleMap 0 t) hmem
    exact ((continuous_circleMap 0 t).mul continuous_const).mul hc
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hbound k _ (hmem θ)) ht.le
  · exact Filter.Eventually.of_forall fun θ _ => hu.mul_left t
  · exact _root_.intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun θ _ => (hgsum _ (hmem θ)).mul_left _

/-- `∮_{|w|=t} w^k dw = 0` for integer `k ≠ -1`. -/
private lemma circleInt_zpow_ne {t : ℝ} (_ht : 0 ≤ t) {k : ℤ} (hk : k ≠ -1) :
    (∮ w in C(0, t), w ^ k) = 0 := by
  have hz := circleIntegral.integral_sub_zpow_of_ne hk 0 0 t
  simpa using hz

/-- `∮_{|w|=t} w⁻¹ dw = 2πi` for `t > 0`. -/
private lemma circleInt_inv {t : ℝ} (ht : 0 < t) :
    (∮ w in C(0, t), w⁻¹) = 2 * ↑π * I := by
  have hz := circleIntegral.integral_sub_inv_of_mem_ball
    (mem_ball_self ht : (0 : ℂ) ∈ ball (0 : ℂ) t)
  simpa using hz

/-- **C1 (shoelace evaluation).**  For the univalent exterior map with Taylor
coefficients `b n`, and `t > 1`,
`shoelace h t = π (t² − ∑' n, n ‖b n‖² (t²)⁻ⁿ)` (a real number, coerced to `ℂ`). -/
theorem shoelace_eval (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (h z))
    {t : ℝ} (ht : 1 < t) :
    shoelace h t
      = ((↑π * ((t ^ 2 : ℝ) - ∑' n : ℕ, (n : ℝ) * ‖b n‖ ^ 2 * ((t ^ 2)⁻¹) ^ n) : ℝ) : ℂ) := by
  have htpos : 0 < t := lt_trans one_pos ht
  have ht0 : (0 : ℝ) ≤ t := htpos.le
  have htinv0 : (0 : ℝ) ≤ t⁻¹ := by positivity
  have htinv1 : t⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; exact ht
  -- sphere facts
  have hwnorm : ∀ w ∈ sphere (0 : ℂ) t, ‖w‖ = t := fun w hw => mem_sphere_zero_iff_norm.mp hw
  have hwne : ∀ w ∈ sphere (0 : ℂ) t, w ≠ 0 := by
    intro w hw
    rw [← norm_pos_iff, hwnorm w hw]; exact htpos
  have hwinv_mem : ∀ w ∈ sphere (0 : ℂ) t, w⁻¹ ∈ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_ball_zero_iff, norm_inv, hwnorm w hw, inv_lt_one_iff₀]; right; exact ht
  have hwinv_norm : ∀ w ∈ sphere (0 : ℂ) t, ‖w⁻¹‖ = t⁻¹ := by
    intro w hw; rw [norm_inv, hwnorm w hw]
  have hconjw : ∀ w ∈ sphere (0 : ℂ) t, (starRingEnd ℂ) w = (t : ℂ) ^ 2 * w⁻¹ := by
    intro w hw
    have hw0 := hwne w hw
    have h1 : w * (starRingEnd ℂ) w = ((t : ℂ)) ^ 2 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, hwnorm w hw]
      push_cast; ring
    have h2 : (starRingEnd ℂ) w = w⁻¹ * (w * (starRingEnd ℂ) w) := by
      rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
    rw [h2, h1]; ring
  -- norm of the zpow monomials on the sphere
  have hnormzpow : ∀ w ∈ sphere (0 : ℂ) t, ∀ n : ℕ, ‖w ^ (-(n : ℤ) - 1)‖ = t⁻¹ ^ (n + 1) := by
    intro w hw n
    rw [show (-(n : ℤ) - 1) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring, zpow_neg, zpow_natCast,
      norm_inv, norm_pow, hwnorm w hw, inv_pow]
  -- the abbreviations
  set S : ℝ := ∑' n : ℕ, (n : ℝ) * ‖b n‖ ^ 2 * ((t ^ 2)⁻¹) ^ n with hSdef
  set Φ : ℂ → ℂ := fun w => (starRingEnd ℂ) (h w⁻¹) with hΦdef
  set Ψ : ℂ → ℂ := fun w => deriv h w⁻¹ * ((w : ℂ) ^ 2)⁻¹ with hΨdef
  set c : ℕ → ℂ := fun m => (starRingEnd ℂ) (b m) * (((t : ℂ) ^ 2)⁻¹) ^ m with hcdef
  -- summable coefficient families
  have s0 : Summable (fun n : ℕ => ‖b n‖ * t⁻¹ ^ n) := by
    have hs := coeff_summable hb 0 htinv0 htinv1
    simpa using hs
  have s1 : Summable (fun n : ℕ => (n : ℝ) * ‖b n‖ * t⁻¹ ^ n) := by
    have hs := coeff_summable hb 1 htinv0 htinv1
    simpa using hs
  set K : ℝ := ∑' m : ℕ, ‖b m‖ * t⁻¹ ^ m with hKdef
  -- Laurent expansions of Φ and Ψ on the sphere
  have hφ : ∀ w ∈ sphere (0 : ℂ) t, HasSum (fun m : ℕ => c m * w ^ m) (Φ w) := by
    intro w hw
    have hstar := (hb w⁻¹ (hwinv_mem w hw)).star
    have hterm : ∀ m : ℕ, c m * w ^ m = (starRingEnd ℂ) (b m * (w⁻¹) ^ m) := by
      intro m
      rw [map_mul, map_pow, map_inv₀, hconjw w hw]
      simp only [hcdef]
      rw [mul_inv, inv_inv, mul_pow]
      ring
    simp only [hΦdef]
    rw [show (fun m : ℕ => c m * w ^ m)
        = fun m : ℕ => (starRingEnd ℂ) (b m * (w⁻¹) ^ m) from funext hterm]
    simpa only [starRingEnd_apply] using hstar
  have hψ : ∀ w ∈ sphere (0 : ℂ) t,
      HasSum (fun n : ℕ => (n : ℂ) * b n * w ^ (-(n : ℤ) - 1)) (Ψ w) := by
    intro w hw
    have hmem := hwinv_mem w hw
    have hn1 : ‖w⁻¹‖ < 1 := by rw [hwinv_norm w hw]; exact htinv1
    have hd : HasSum (fun n : ℕ => (n : ℂ) * b n * (w⁻¹) ^ (n - 1)) (deriv h w⁻¹) := by
      rw [(h_hasDerivAt hb hmem).deriv]
      exact (deriv_family_summable hb hn1).hasSum
    have hdm := hd.mul_right (((w : ℂ) ^ 2)⁻¹)
    have hterm : ∀ n : ℕ, (n : ℂ) * b n * w ^ (-(n : ℤ) - 1)
        = (n : ℂ) * b n * (w⁻¹) ^ (n - 1) * ((w : ℂ) ^ 2)⁻¹ := by
      intro n
      cases n with
      | zero => simp
      | succ m =>
        have he : (-((m + 1 : ℕ) : ℤ) - 1) = -(((m + 2 : ℕ) : ℤ)) := by push_cast; ring
        have h2 : w ^ (-((m + 1 : ℕ) : ℤ) - 1) = (w⁻¹) ^ m * ((w : ℂ) ^ 2)⁻¹ := by
          rw [he, zpow_neg, zpow_natCast, pow_add, mul_inv, ← inv_pow]
        rw [Nat.add_sub_cancel, h2]
        ring
    simp only [hΨdef]
    rw [show (fun n : ℕ => (n : ℂ) * b n * w ^ (-(n : ℤ) - 1))
        = fun n : ℕ => (n : ℂ) * b n * (w⁻¹) ^ (n - 1) * ((w : ℂ) ^ 2)⁻¹ from funext hterm]
    exact hdm
  -- continuity on the sphere
  have hcont_inv : ContinuousOn (fun w : ℂ => w⁻¹) (sphere (0 : ℂ) t) :=
    ContinuousOn.inv₀ continuousOn_id (fun w hw => hwne w hw)
  have hmaps : MapsTo (fun w : ℂ => w⁻¹) (sphere (0 : ℂ) t) (ball (0 : ℂ) 1) :=
    fun w hw => hwinv_mem w hw
  have hcont_h : ContinuousOn (fun w : ℂ => h w⁻¹) (sphere (0 : ℂ) t) :=
    (hh.continuousOn).comp hcont_inv hmaps
  have hcontΦ : ContinuousOn Φ (sphere (0 : ℂ) t) := by
    have hc := continuous_star.comp_continuousOn hcont_h
    simp only [hΦdef]
    simpa only [Function.comp_def, starRingEnd_apply] using hc
  have hcont_dh : ContinuousOn (fun w : ℂ => deriv h w⁻¹) (sphere (0 : ℂ) t) :=
    (hh.deriv.continuousOn).comp hcont_inv hmaps
  have hcont_sq : ContinuousOn (fun w : ℂ => ((w : ℂ) ^ 2)⁻¹) (sphere (0 : ℂ) t) :=
    ContinuousOn.inv₀ (continuousOn_id.pow 2) (fun w hw => pow_ne_zero 2 (hwne w hw))
  have hcontΨ : ContinuousOn Ψ (sphere (0 : ℂ) t) := by
    simp only [hΨdef]
    exact hcont_dh.mul hcont_sq
  have hcont_zpow : ∀ k : ℤ, ContinuousOn (fun w : ℂ => w ^ k) (sphere (0 : ℂ) t) :=
    fun k => ContinuousOn.zpow₀ continuousOn_id k (fun w hw => Or.inl (hwne w hw))
  -- uniform bound for Φ on the sphere
  have hK0 : 0 ≤ K := tsum_nonneg fun m => by positivity
  have hΦbound : ∀ w ∈ sphere (0 : ℂ) t, ‖Φ w‖ ≤ K := by
    intro w hw
    have hsum := hb w⁻¹ (hwinv_mem w hw)
    have hnorm_eq : ∀ m : ℕ, ‖b m * (w⁻¹) ^ m‖ = ‖b m‖ * t⁻¹ ^ m := by
      intro m; rw [norm_mul, norm_pow, hwinv_norm w hw]
    have hsn : Summable (fun m : ℕ => ‖b m * (w⁻¹) ^ m‖) :=
      s0.congr fun m => (hnorm_eq m).symm
    have h1 : ‖Φ w‖ = ‖h w⁻¹‖ := by
      simp only [hΦdef]
      exact Complex.norm_conj _
    rw [h1, ← hsum.tsum_eq]
    calc ‖∑' m, b m * (w⁻¹) ^ m‖ ≤ ∑' m, ‖b m * (w⁻¹) ^ m‖ := norm_tsum_le_tsum_norm hsn
      _ = K := by rw [hKdef]; exact tsum_congr hnorm_eq
  -- the four integral evaluations
  have hI1 : (∮ w in C(0, t), (t : ℂ) ^ 2 * w⁻¹) = (t : ℂ) ^ 2 * (2 * ↑π * I) := by
    rw [circleIntegral.integral_const_mul, circleInt_inv htpos]
  have hbase : (t ^ 2)⁻¹ * t = t⁻¹ := by
    rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ htpos.ne', mul_one]
  have hnorm_t2 : ‖(((t : ℂ)) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hI2 : (∮ w in C(0, t), Φ w) = 0 := by
    have hbndB : ∀ m : ℕ, ∀ w ∈ sphere (0 : ℂ) t, ‖c m * w ^ m‖ ≤ ‖b m‖ * t⁻¹ ^ m := by
      intro m w hw
      refine le_of_eq ?_
      simp only [hcdef]
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, hnorm_t2, hwnorm w hw,
        mul_assoc, ← mul_pow, hbase]
    have hHSB := hasSum_circleIntegral_of_bound htpos (fun m w => c m * w ^ m) Φ
      (fun m => ‖b m‖ * t⁻¹ ^ m) s0
      (fun m => continuousOn_const.mul ((continuous_pow m).continuousOn)) hbndB hφ
    have hevB : ∀ m : ℕ, (∮ w in C(0, t), c m * w ^ m) = 0 := by
      intro m
      have hcongr : EqOn (fun w : ℂ => c m * w ^ m) (fun w : ℂ => c m * w ^ (m : ℤ))
          (sphere (0 : ℂ) t) := by
        intro w _
        show c m * w ^ m = c m * w ^ (m : ℤ)
        rw [zpow_natCast]
      rw [circleIntegral.integral_congr ht0 hcongr, circleIntegral.integral_const_mul,
        circleInt_zpow_ne ht0 (by omega : (m : ℤ) ≠ -1), mul_zero]
    have h0B : HasSum (fun m : ℕ => (∮ w in C(0, t), c m * w ^ m)) 0 := by
      rw [show (fun m : ℕ => (∮ w in C(0, t), c m * w ^ m)) = fun _ : ℕ => (0 : ℂ) from
        funext hevB]
      exact hasSum_zero
    exact hHSB.unique h0B
  have hI3 : (∮ w in C(0, t), (t : ℂ) ^ 2 * (w⁻¹ * Ψ w)) = 0 := by
    rw [circleIntegral.integral_const_mul]
    suffices hs : (∮ w in C(0, t), w⁻¹ * Ψ w) = 0 by rw [hs, mul_zero]
    have hgsumC : ∀ w ∈ sphere (0 : ℂ) t,
        HasSum (fun n : ℕ => w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))) (w⁻¹ * Ψ w) :=
      fun w hw => (hψ w hw).mul_left _
    have hbndC : ∀ n : ℕ, ∀ w ∈ sphere (0 : ℂ) t,
        ‖w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))‖
          ≤ t⁻¹ * ((n : ℝ) * ‖b n‖ * t⁻¹ ^ (n + 1)) := by
      intro n w hw
      refine le_of_eq ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, hwinv_norm w hw,
        hnormzpow w hw n]
    have huC : Summable (fun n : ℕ => t⁻¹ * ((n : ℝ) * ‖b n‖ * t⁻¹ ^ (n + 1))) := by
      refine Summable.congr (s1.mul_left (t⁻¹ * t⁻¹)) fun n => ?_
      ring
    have hcontC : ∀ n : ℕ, ContinuousOn
        (fun w : ℂ => w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))) (sphere (0 : ℂ) t) :=
      fun n => hcont_inv.mul (continuousOn_const.mul (hcont_zpow _))
    have hHSC := hasSum_circleIntegral_of_bound htpos
      (fun n w => w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))) (fun w => w⁻¹ * Ψ w)
      (fun n => t⁻¹ * ((n : ℝ) * ‖b n‖ * t⁻¹ ^ (n + 1))) huC hcontC hbndC hgsumC
    have hevC : ∀ n : ℕ,
        (∮ w in C(0, t), w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))) = 0 := by
      intro n
      have hcongr : EqOn (fun w : ℂ => w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1)))
          (fun w : ℂ => ((n : ℂ) * b n) * w ^ (-(n : ℤ) - 2)) (sphere (0 : ℂ) t) := by
        intro w hw
        have hw0 := hwne w hw
        show w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1)) = ((n : ℂ) * b n) * w ^ (-(n : ℤ) - 2)
        rw [show (-(n : ℤ) - 2) = (-1) + (-(n : ℤ) - 1) by ring, zpow_add₀ hw0, zpow_neg_one]
        ring
      rw [circleIntegral.integral_congr ht0 hcongr, circleIntegral.integral_const_mul,
        circleInt_zpow_ne ht0 (by omega : (-(n : ℤ) - 2) ≠ -1), mul_zero]
    have h0C : HasSum
        (fun n : ℕ => (∮ w in C(0, t), w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1)))) 0 := by
      rw [show (fun n : ℕ => (∮ w in C(0, t), w⁻¹ * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))))
          = fun _ : ℕ => (0 : ℂ) from funext hevC]
      exact hasSum_zero
    exact hHSC.unique h0C
  -- the diagonal term
  have hinner : ∀ n : ℕ,
      (∮ w in C(0, t), Φ w * w ^ (-(n : ℤ) - 1)) = 2 * ↑π * I * c n := by
    intro n
    have hgsumI : ∀ w ∈ sphere (0 : ℂ) t,
        HasSum (fun m : ℕ => c m * w ^ m * w ^ (-(n : ℤ) - 1)) (Φ w * w ^ (-(n : ℤ) - 1)) :=
      fun w hw => (hφ w hw).mul_right _
    have hbndI : ∀ m : ℕ, ∀ w ∈ sphere (0 : ℂ) t,
        ‖c m * w ^ m * w ^ (-(n : ℤ) - 1)‖ ≤ t⁻¹ ^ (n + 1) * (‖b m‖ * t⁻¹ ^ m) := by
      intro m w hw
      refine le_of_eq ?_
      rw [norm_mul, hnormzpow w hw n]
      simp only [hcdef]
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, hnorm_t2, hwnorm w hw]
      have hcancel : t⁻¹ ^ m * t ^ m = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ htpos.ne', one_pow]
      have hsplit2 : ((t ^ 2)⁻¹ : ℝ) ^ m = t⁻¹ ^ m * t⁻¹ ^ m := by
        rw [← mul_pow, pow_two, mul_inv]
      rw [hsplit2]
      linear_combination (‖b m‖ * t⁻¹ ^ m * t⁻¹ ^ (n + 1)) * hcancel
    have huI : Summable (fun m : ℕ => t⁻¹ ^ (n + 1) * (‖b m‖ * t⁻¹ ^ m)) :=
      s0.mul_left _
    have hcontI : ∀ m : ℕ, ContinuousOn
        (fun w : ℂ => c m * w ^ m * w ^ (-(n : ℤ) - 1)) (sphere (0 : ℂ) t) :=
      fun m => (continuousOn_const.mul ((continuous_pow m).continuousOn)).mul (hcont_zpow _)
    have hHSI := hasSum_circleIntegral_of_bound htpos
      (fun m w => c m * w ^ m * w ^ (-(n : ℤ) - 1)) (fun w => Φ w * w ^ (-(n : ℤ) - 1))
      (fun m => t⁻¹ ^ (n + 1) * (‖b m‖ * t⁻¹ ^ m)) huI hcontI hbndI hgsumI
    have hevI : ∀ m : ℕ, (∮ w in C(0, t), c m * w ^ m * w ^ (-(n : ℤ) - 1))
        = if m = n then 2 * ↑π * I * c n else 0 := by
      intro m
      have hcongr : EqOn (fun w : ℂ => c m * w ^ m * w ^ (-(n : ℤ) - 1))
          (fun w : ℂ => c m * w ^ ((m : ℤ) - (n : ℤ) - 1)) (sphere (0 : ℂ) t) := by
        intro w hw
        have hw0 := hwne w hw
        show c m * w ^ m * w ^ (-(n : ℤ) - 1) = c m * w ^ ((m : ℤ) - (n : ℤ) - 1)
        rw [show ((m : ℤ) - (n : ℤ) - 1) = (m : ℤ) + (-(n : ℤ) - 1) by ring,
          zpow_add₀ hw0, zpow_natCast]
        ring
      rw [circleIntegral.integral_congr ht0 hcongr, circleIntegral.integral_const_mul]
      by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, show ((m : ℤ) - (m : ℤ) - 1) = (-1 : ℤ) by ring]
        have hminus : (∮ w in C(0, t), w ^ (-1 : ℤ)) = ∮ w in C(0, t), w⁻¹ :=
          circleIntegral.integral_congr ht0 fun w _ => zpow_neg_one w
        rw [hminus, circleInt_inv htpos]
        ring
      · rw [if_neg hmn,
          circleInt_zpow_ne ht0 (by omega : ((m : ℤ) - (n : ℤ) - 1) ≠ -1), mul_zero]
    have h0I : HasSum (fun m : ℕ => (∮ w in C(0, t), c m * w ^ m * w ^ (-(n : ℤ) - 1)))
        (2 * ↑π * I * c n) := by
      rw [show (fun m : ℕ => (∮ w in C(0, t), c m * w ^ m * w ^ (-(n : ℤ) - 1)))
          = fun m : ℕ => if m = n then 2 * ↑π * I * c n else 0 from funext hevI]
      exact hasSum_ite_eq n _
    exact hHSI.unique h0I
  -- the S-summability facts
  have hsummS : Summable (fun n : ℕ => (n : ℝ) * ‖b n‖ ^ 2 * ((t ^ 2)⁻¹) ^ n) := by
    have h20 : (0 : ℝ) ≤ (t ^ 2)⁻¹ := by positivity
    have h21 : ((t ^ 2)⁻¹ : ℝ) < 1 := by
      rw [inv_lt_one_iff₀]; right; nlinarith
    have hs := coeff_sq_summable hb 1 h20 h21
    simpa using hs
  have hSsum : HasSum (fun n : ℕ => (n : ℝ) * ‖b n‖ ^ 2 * ((t ^ 2)⁻¹) ^ n) S := by
    rw [hSdef]; exact hsummS.hasSum
  have hI4 : (∮ w in C(0, t), Φ w * Ψ w) = 2 * ↑π * I * (S : ℂ) := by
    have hgsumO : ∀ w ∈ sphere (0 : ℂ) t,
        HasSum (fun n : ℕ => Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))) (Φ w * Ψ w) :=
      fun w hw => (hψ w hw).mul_left _
    have hbndO : ∀ n : ℕ, ∀ w ∈ sphere (0 : ℂ) t,
        ‖Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))‖
          ≤ K * ((n : ℝ) * ‖b n‖ * t⁻¹ ^ (n + 1)) := by
      intro n w hw
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, hnormzpow w hw n]
      exact mul_le_mul_of_nonneg_right (hΦbound w hw) (by positivity)
    have huO : Summable (fun n : ℕ => K * ((n : ℝ) * ‖b n‖ * t⁻¹ ^ (n + 1))) := by
      refine Summable.congr (s1.mul_left (K * t⁻¹)) fun n => ?_
      ring
    have hcontO : ∀ n : ℕ, ContinuousOn
        (fun w : ℂ => Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))) (sphere (0 : ℂ) t) :=
      fun n => hcontΦ.mul (continuousOn_const.mul (hcont_zpow _))
    have hHSO := hasSum_circleIntegral_of_bound htpos
      (fun n w => Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))) (fun w => Φ w * Ψ w)
      (fun n => K * ((n : ℝ) * ‖b n‖ * t⁻¹ ^ (n + 1))) huO hcontO hbndO hgsumO
    have hevO : ∀ n : ℕ, (∮ w in C(0, t), Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1)))
        = (n : ℂ) * b n * (2 * ↑π * I * c n) := by
      intro n
      have hcongr : EqOn (fun w : ℂ => Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1)))
          (fun w : ℂ => ((n : ℂ) * b n) * (Φ w * w ^ (-(n : ℤ) - 1))) (sphere (0 : ℂ) t) := by
        intro w _
        show Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))
          = ((n : ℂ) * b n) * (Φ w * w ^ (-(n : ℤ) - 1))
        ring
      rw [circleIntegral.integral_congr ht0 hcongr, circleIntegral.integral_const_mul,
        hinner n]
    have hSC : HasSum (fun n : ℕ => (((n : ℝ) * ‖b n‖ ^ 2 * ((t ^ 2)⁻¹) ^ n : ℝ) : ℂ))
        ((S : ℝ) : ℂ) := Complex.hasSum_ofReal.mpr hSsum
    have hmulS := hSC.mul_left (2 * ↑π * I)
    have hfeq : (fun n : ℕ => (n : ℂ) * b n * (2 * ↑π * I * c n))
        = fun n : ℕ => (2 * ↑π * I) * (((n : ℝ) * ‖b n‖ ^ 2 * ((t ^ 2)⁻¹) ^ n : ℝ) : ℂ) := by
      funext n
      simp only [hcdef]
      have hb2 : ((‖b n‖ : ℂ)) ^ 2 = b n * (starRingEnd ℂ) (b n) := by
        rw [show ((‖b n‖ : ℂ)) ^ 2 = ((‖b n‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.sq_norm, Complex.mul_conj]
      push_cast
      rw [hb2]
      ring
    have hfinal : HasSum (fun n : ℕ => (n : ℂ) * b n * (2 * ↑π * I * c n))
        (2 * ↑π * I * (S : ℂ)) := by
      rw [hfeq]; exact hmulS
    have h0O : HasSum (fun n : ℕ => (∮ w in C(0, t), Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))))
        (2 * ↑π * I * (S : ℂ)) := by
      rw [show (fun n : ℕ => (∮ w in C(0, t), Φ w * ((n : ℂ) * b n * w ^ (-(n : ℤ) - 1))))
          = fun n : ℕ => (n : ℂ) * b n * (2 * ↑π * I * c n) from funext hevO]
      exact hfinal
    exact hHSO.unique h0O
  -- decompose the shoelace integrand on the sphere
  have hsplit : (∮ w in C(0, t), (starRingEnd ℂ) (extMap h w) * deriv (extMap h) w)
      = ∮ w in C(0, t),
          ((t : ℂ) ^ 2 * w⁻¹ + Φ w - ((t : ℂ) ^ 2 * (w⁻¹ * Ψ w) + Φ w * Ψ w)) := by
    apply circleIntegral.integral_congr ht0
    intro w hw
    have hw1 : 1 < ‖w‖ := by rw [hwnorm w hw]; exact ht
    show (starRingEnd ℂ) (extMap h w) * deriv (extMap h) w
      = (t : ℂ) ^ 2 * w⁻¹ + Φ w - ((t : ℂ) ^ 2 * (w⁻¹ * Ψ w) + Φ w * Ψ w)
    rw [extMap_deriv_eq hb hw1]
    simp only [extMap, hΦdef, hΨdef]
    rw [map_add, hconjw w hw]
    ring
  -- circle integrability of the pieces
  have hciA : CircleIntegrable (fun w : ℂ => (t : ℂ) ^ 2 * w⁻¹) 0 t :=
    ContinuousOn.circleIntegrable ht0 (continuousOn_const.mul hcont_inv)
  have hciB : CircleIntegrable Φ 0 t := ContinuousOn.circleIntegrable ht0 hcontΦ
  have hciC : CircleIntegrable (fun w : ℂ => (t : ℂ) ^ 2 * (w⁻¹ * Ψ w)) 0 t :=
    ContinuousOn.circleIntegrable ht0 (continuousOn_const.mul (hcont_inv.mul hcontΨ))
  have hciD : CircleIntegrable (fun w : ℂ => Φ w * Ψ w) 0 t :=
    ContinuousOn.circleIntegrable ht0 (hcontΦ.mul hcontΨ)
  have hciAB : CircleIntegrable (fun w : ℂ => (t : ℂ) ^ 2 * w⁻¹ + Φ w) 0 t :=
    ContinuousOn.circleIntegrable ht0 ((continuousOn_const.mul hcont_inv).add hcontΦ)
  have hciCD : CircleIntegrable (fun w : ℂ => (t : ℂ) ^ 2 * (w⁻¹ * Ψ w) + Φ w * Ψ w) 0 t :=
    ContinuousOn.circleIntegrable ht0
      ((continuousOn_const.mul (hcont_inv.mul hcontΨ)).add (hcontΦ.mul hcontΨ))
  -- assemble
  rw [shoelace, hsplit, circleIntegral.integral_sub hciAB hciCD,
    circleIntegral.integral_add hciA hciB, circleIntegral.integral_add hciC hciD,
    hI1, hI2, hI3, hI4, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]
  have h2I : (2 * I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  field_simp
  ring

end Uniformization
