import Uniformization.Complex.AreaIntegral
import Mathlib.Analysis.Calculus.SmoothSeries

open Set Metric Complex MeasureTheory Topology Filter Real intervalIntegral

noncomputable section

namespace Uniformization

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

end Uniformization
