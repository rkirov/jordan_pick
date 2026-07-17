/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Order.OrderClosed
import Uniformization.Complex.AreaEval

/-!
# The area theorem (Grönwall) for univalent functions

Stage 1 of the Koebe chain (`Uniformization/Complex/Koebe.lean`).

Let `h` be analytic on the open unit ball with Taylor expansion
`h z = ∑ n, b n * z ^ n`, and suppose the map `g z = z⁻¹ + h z` is injective on
the punctured unit ball `ball 0 1 \ {0}` (equivalently, in exterior coordinates
`w = 1/z`, the map `G w = w + ∑ n, b n * w⁻ⁿ` is univalent on `{|w| > 1}`).

The **area theorem** states, in the finite-partial-sum form that Bieberbach needs
(no summability side conditions):

  `area_theorem : ∀ N, ∑ n ∈ Finset.range (N+1), n * ‖b n‖² ≤ 1`.

## Proof route

The classical Grönwall proof. Fix a radius `t > 1` (equivalently `ρ = 1/t ∈ (0,1)`
in interior coordinates). The image circle `Γ_t := G '' {|w| = t}` is a `C¹` Jordan
curve (`G` is injective and holomorphic); it bounds the compact complement
`E_t := ℂ \ G '' {|w| > t}`. Two computations of the enclosed area agree:

* **Shoelace / Green** (contour side). By Green's theorem the enclosed area equals
  `(2i)⁻¹ ∮_{|w|=t} conj(G) G' dw`, and termwise integration of the Laurent series
  (angular orthogonality `∫₀^{2π} e^{ikθ} dθ = 0`, `k ≠ 0`) evaluates this to

    `area(E_t) = π (t² − ∑' n, n ‖b n‖² t^{-2n})`.

* **Positivity** (geometric side). `area(E_t) ≥ 0`, since it is the Lebesgue measure
  of the bounded set `E_t`. Equivalently `area(E_t) = ∫_ℂ wind(Γ_t, ·)` with
  `wind(Γ_t, ·) = 𝟙_{E_t}` a.e. (winding of a `C¹` loop, computed by the annulus
  argument principle), and `∫_ℂ wind(Γ_t, ·) = shoelace(t)` by Fubini against the
  Cauchy transform of the disk.

Combining, `∑' n, n ‖b n‖² t^{-2n} ≤ t²`, i.e. in interior coordinates
`∑ n, n ‖b n‖² ρ^{2n} ≤ ρ⁻²` for every `ρ ∈ (0,1)`.  Truncating to a finite range
(dropped terms are nonnegative) and letting `ρ → 1⁻` gives
`∑ n ∈ range (N+1), n ‖b n‖² ≤ 1`.

## Status

**Sorry-free.**  The per-radius inequality `groenwall_radius` is discharged from the
winding/shoelace development: the winding-number layer (A1–A4) is built in
`AreaWinding.lean`, the area/shoelace Fubini identity (Stage B) in
`AreaIntegral.lean`, and the shoelace evaluation plus the positivity argument
(Stages C1–C3) in `AreaEval.lean`, whose `coeff_tsum_le_sq` is exactly the
exterior-coordinate form `∑' n, n ‖b n‖² t^{-2n} ≤ t²` used here after the
substitution `t = 1/ρ` and truncation.  The `ρ → 1⁻` limit yielding the
finite-form `area_theorem` closes the chain.

The coefficient encoding follows the task's "`h` given by a power series" option:
`hb` supplies the Taylor coefficients `b n` directly as a `HasSum` on the whole ball
(at `z = 0` the `n ≥ 1` terms vanish, pinning `b 0 = h 0`).
-/

open Set Metric Filter Topology MeasureTheory

namespace Uniformization

/-- **Per-radius Grönwall inequality** (geometric core).

For the univalent `g z = z⁻¹ + h z` with Taylor coefficients `b n` of `h`, and every
`ρ ∈ (0,1)`, the truncated coefficient energy is bounded by `ρ⁻²`:

  `∑ n ∈ range (N+1), n ‖b n‖² ρ^{2n} ≤ ρ⁻²`.

In exterior coordinates `t = 1/ρ > 1` this is `∑ n, n ‖b n‖² t^{-2n} ≤ t²`, which is
`area(E_t) ≥ 0` after the shoelace evaluation
`area(E_t) = π (t² − ∑ n, n ‖b n‖² t^{-2n})` — supplied by `coeff_tsum_le_sq`
(`AreaEval.lean`). -/
theorem groenwall_radius {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Metric.ball 0 1))
    {b : ℕ → ℂ} (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (h z))
    (hinj : Set.InjOn (fun z => z⁻¹ + h z) (Metric.ball 0 1 \ {0}))
    (N : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖b n‖ ^ 2 * ρ ^ (2 * n) ≤ (ρ ^ 2)⁻¹ := by
  have ht : 1 < ρ⁻¹ := (one_lt_inv₀ hρ0).mpr hρ1
  -- the full-series bound in exterior coordinates, `t = ρ⁻¹`
  have hkey := coeff_tsum_le_sq hh hb hinj ht
  -- summability of the full series (`(ρ⁻¹²)⁻¹ = ρ² < 1`)
  have h20 : (0 : ℝ) ≤ (ρ⁻¹ ^ 2)⁻¹ := by positivity
  have h21 : ((ρ⁻¹ ^ 2)⁻¹ : ℝ) < 1 := by
    rw [inv_lt_one_iff₀]; right; nlinarith
  have hsummS : Summable (fun n : ℕ => (n : ℝ) * ‖b n‖ ^ 2 * ((ρ⁻¹ ^ 2)⁻¹) ^ n) := by
    have hs := coeff_sq_summable hb 1 h20 h21
    simpa using hs
  have htrunc := hsummS.sum_le_tsum (Finset.range (N + 1)) (fun i _ => by positivity)
  have hρt : ((ρ⁻¹ ^ 2)⁻¹ : ℝ) = ρ ^ 2 := by rw [inv_pow, inv_inv]
  calc ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖b n‖ ^ 2 * ρ ^ (2 * n)
      = ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖b n‖ ^ 2 * ((ρ⁻¹ ^ 2)⁻¹) ^ n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hρt, pow_mul]
    _ ≤ ∑' n : ℕ, (n : ℝ) * ‖b n‖ ^ 2 * ((ρ⁻¹ ^ 2)⁻¹) ^ n := htrunc
    _ ≤ ρ⁻¹ ^ 2 := hkey
    _ = (ρ ^ 2)⁻¹ := by rw [inv_pow]

/-- **The area theorem** (Grönwall), finite-partial-sum form.

If `h` is analytic on the unit ball with Taylor coefficients `b n`
(`h z = ∑ n, b n z ^ n`) and `g z = z⁻¹ + h z` is injective on the punctured unit
ball, then for every `N`,

  `∑ n ∈ Finset.range (N+1), n ‖b n‖² ≤ 1`.

This is exactly the input Bieberbach's `‖a₂‖ ≤ 2` needs, and it carries no
summability side conditions. -/
theorem area_theorem {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Metric.ball 0 1))
    {b : ℕ → ℂ} (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (h z))
    (hinj : Set.InjOn (fun z => z⁻¹ + h z) (Metric.ball 0 1 \ {0})) :
    ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖b n‖ ^ 2 ≤ 1 := by
  intro N
  -- The finite coefficient-energy polynomial in the radius.
  set F : ℝ → ℝ := fun ρ => ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖b n‖ ^ 2 * ρ ^ (2 * n)
    with hF
  -- `F` is continuous (a finite sum of monomials).
  have hFcont : Continuous F := by
    apply continuous_finsetSum
    intro n _
    exact (continuous_const.mul (continuous_pow (2 * n)))
  -- `F 1` is the target left-hand side.
  have hF1 : F 1 = ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖b n‖ ^ 2 := by
    simp [hF]
  -- `G ρ := (ρ²)⁻¹` is the per-radius bound; `G 1 = 1`.
  set G : ℝ → ℝ := fun ρ => (ρ ^ 2)⁻¹ with hG
  have hGcontAt : ContinuousAt G 1 := by
    apply ContinuousAt.inv₀
    · exact (continuous_pow 2).continuousAt
    · norm_num
  have hG1 : G 1 = 1 := by simp [hG]
  -- Tendsto along `𝓝[<] 1`.
  have hFtend : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (F 1)) :=
    (hFcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hGtend : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 (G 1)) :=
    hGcontAt.tendsto.mono_left nhdsWithin_le_nhds
  -- On `(0,1)` near `1` the per-radius inequality gives `F ≤ G`.
  have hpos : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), (0 : ℝ) < ρ :=
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hev : F ≤ᶠ[𝓝[<] (1 : ℝ)] G := by
    filter_upwards [self_mem_nhdsWithin, hpos] with ρ hρ1 hρ0
    rw [mem_Iio] at hρ1
    exact groenwall_radius hh hb hinj N hρ0 hρ1
  -- Pass to the limit `ρ → 1⁻`.
  have := le_of_tendsto_of_tendsto hFtend hGtend hev
  rwa [hF1, hG1] at this

end Uniformization
