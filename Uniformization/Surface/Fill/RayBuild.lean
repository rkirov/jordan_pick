/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.RayCollar

/-!
# Building a ray-collar datum from raw tube coordinates (W7 step L5.5–L6, part A)

`RayCollar.lean` isolates the *analytic packaging* of the per-end collapse behind
the structure `RayCollar`, and `exists_end_collapse_of_rayCollar` reduces the
remaining geometric input (`exists_end_collapse`) to *producing* a `RayCollar` for
every end.  This file performs the next reduction: it factors the collar-coordinate
*model* out of the geometry.

The `RayCollar` fields `dm, dp` are, in the intended model (see the `RayCollar`
docstring), the concrete functions

* `dm x = ε · s · χ(t)` on the minus half-collar,
* `dp x = 1 − ε · s · χ(t)` on the plus half-collar,

where `(t, s)` are the tube coordinates along / transverse to the cutting ray and
`χ` is a corner cutoff (`χ 0 = 1`, `χ ≡ 0` for `t ≥ 1`) that kills the collar data
beyond the corner rectangle.  This file:

* defines the corner cutoff `cornerCutoff` and records its elementary properties;
* packages the *geometric* output of part A as `TubeData` — closed half-collars
  `Sm, Sp` sharing a ray edge `R`, equipped with **raw continuous coordinate
  functions** `sm, tm` (resp. `sp, tp`), their edge relations to `γ` at the circle
  edge, and the neighbourhood-coverage facts;
* proves `rayCollar_of_tubeData : TubeData … → RayCollar …`, computing `dm, dp` by
  the model formula and discharging every `RayCollar` field.

Thus the *sole* remaining geometric obligation for part A is to construct a
`TubeData` value: an embedded proper cutting ray with a two-sided tubular
neighbourhood whose transverse coordinate matches `γ` at the boundary circle.  All
coordinate bookkeeping (`dm, dp` continuity, range `⊆ [0,1]`, ray values `0`/`1`,
and the corner matching `γ (dm x) = x`) is discharged here, once and for all.
-/

open Set Topology Filter

namespace Uniformization

/-! ## The corner cutoff -/

/-- **Corner cutoff.**  `cornerCutoff t = max 0 (1 - t)`: it equals `1` at `t = 0`,
decreases linearly, and vanishes for `t ≥ 1`.  In the collar model it multiplies
the transverse coordinate so that the collar data is nontrivial only on the corner
rectangle (`t ∈ [0,1]`) and identically trivial (`dm = 0`, `dp = 1`) beyond it. -/
noncomputable def cornerCutoff (t : ℝ) : ℝ := max 0 (1 - t)

theorem cornerCutoff_zero : cornerCutoff 0 = 1 := by simp [cornerCutoff]

theorem cornerCutoff_nonneg (t : ℝ) : 0 ≤ cornerCutoff t := le_max_left _ _

theorem cornerCutoff_le_one {t : ℝ} (ht : 0 ≤ t) : cornerCutoff t ≤ 1 := by
  rw [cornerCutoff, max_le_iff]; exact ⟨zero_le_one, by linarith⟩

theorem continuous_cornerCutoff : Continuous cornerCutoff := by
  unfold cornerCutoff; fun_prop

/-! ## Tube data: the geometric output of part A -/

/-- **Raw tube datum for the cutting ray of one complement end.**  This is the
geometric payload part A must produce; `rayCollar_of_tubeData` turns it into a
`RayCollar`.

Compared with `RayCollar`, the collar *coordinates* are given here in their raw
tube form: continuous functions `sm, tm` on the minus half-collar `Sm`
(transverse coordinate `sm ∈ [0,1]`, along-ray coordinate `tm ≥ 0`) and likewise
`sp, tp` on `Sp`, subject only to their edge relations:

* on the ray edge `R`, the transverse coordinate vanishes (`sm = 0`, `sp = 0`);
* on the circle edge `Sm ∩ CZ` (resp. `Sp ∩ CZ`) the along-ray coordinate vanishes
  (`tm = 0`) and the transverse coordinate parametrises `γ`
  (`γ (ε · sm x) = x`, resp. `γ (1 - ε · sp x) = x`).

All set-theoretic facts (`closedness`, containments, the thin-overlap `hSmSp`) and
the neighbourhood-coverage facts (`hCZcover`, `hcov`, `hcovp`) are as in
`RayCollar`. -/
structure TubeData (X : Type*) [TopologicalSpace X] (Z CZ : Set X) (γ : ℝ → X)
    (p : X) where
  /-- Shared ray edge of the two half-collars. -/
  R : Set X
  /-- Minus half-collar. -/
  Sm : Set X
  /-- Plus half-collar. -/
  Sp : Set X
  /-- Transverse coordinate on `Sm` (`0` on the ray, `∈ [0,1]`). -/
  sm : X → ℝ
  /-- Along-ray coordinate on `Sm` (`≥ 0`, `0` at the circle edge). -/
  tm : X → ℝ
  /-- Transverse coordinate on `Sp`. -/
  sp : X → ℝ
  /-- Along-ray coordinate on `Sp`. -/
  tp : X → ℝ
  /-- Half-width of the two circle arcs cut out by the collars. -/
  ε : ℝ
  hε : 0 < ε
  hε1 : ε < 1
  hRcl : IsClosed R
  hSmcl : IsClosed Sm
  hSpcl : IsClosed Sp
  hpR : p ∈ R
  hRSm : R ⊆ Sm
  hRSp : R ⊆ Sp
  hRZ : R \ {p} ⊆ Z
  hSmZ : Sm ⊆ Z ∪ CZ
  hSpZ : Sp ⊆ Z ∪ CZ
  hSmSp : Sm ∩ Sp ⊆ R
  hsm_cont : ContinuousOn sm Sm
  htm_cont : ContinuousOn tm Sm
  hsp_cont : ContinuousOn sp Sp
  htp_cont : ContinuousOn tp Sp
  hsm_mem : ∀ x ∈ Sm, sm x ∈ Set.Icc (0 : ℝ) 1
  htm_nonneg : ∀ x ∈ Sm, 0 ≤ tm x
  hsp_mem : ∀ x ∈ Sp, sp x ∈ Set.Icc (0 : ℝ) 1
  htp_nonneg : ∀ x ∈ Sp, 0 ≤ tp x
  hsm_R : ∀ x ∈ R, sm x = 0
  hsp_R : ∀ x ∈ R, sp x = 0
  hCZm : ∀ x ∈ Sm ∩ CZ, tm x = 0 ∧ γ (ε * sm x) = x
  hCZp : ∀ x ∈ Sp ∩ CZ, tp x = 0 ∧ γ (1 - ε * sp x) = x
  hCZcover : CZ ⊆ Sm ∪ Sp ∪ γ '' Set.Icc ε (1 - ε)
  hcov : ∀ r ∈ R \ {p}, ∀ᶠ x in 𝓝 r, x ∈ Sm ∪ Sp
  hcovp : ∀ᶠ x in 𝓝 p, x ∈ Z → x ∈ Sm ∪ Sp

/-! ## The packaging reduction -/

/-- **From raw tube data to a ray-collar datum.**  Given a `TubeData`, the collar
coordinates of the intended model

* `dm x = ε · (sm x) · χ (tm x)`,
* `dp x = 1 − ε · (sp x) · χ (tp x)`

(with `χ = cornerCutoff`) satisfy every `RayCollar` field: continuity is
composition of the continuous coordinates with `χ`; the range `⊆ [0,1]` is a
product of factors in `[0,1]`; on the ray edge `sm = sp = 0` gives `dm = 0`,
`dp = 1`; and on the circle edge `tm = tp = 0` gives `χ = 1`, so `dm = ε·sm`,
`dp = 1 − ε·sp`, whence the corner matching `γ (dm x) = x` is exactly `hCZm`/`hCZp`.

This discharges all collar-coordinate bookkeeping, leaving only the construction of
a `TubeData` (an embedded proper cutting ray with a two-sided tubular
neighbourhood) as the geometric content of part A. -/
noncomputable def rayCollar_of_tubeData {X : Type*} [TopologicalSpace X]
    {Z CZ : Set X} {γ : ℝ → X} {p : X} (td : TubeData X Z CZ γ p) :
    RayCollar X Z CZ γ p where
  R := td.R
  Sm := td.Sm
  Sp := td.Sp
  dm := fun x => td.ε * td.sm x * cornerCutoff (td.tm x)
  dp := fun x => 1 - td.ε * td.sp x * cornerCutoff (td.tp x)
  ε := td.ε
  hε := td.hε
  hε1 := td.hε1
  hRcl := td.hRcl
  hSmcl := td.hSmcl
  hSpcl := td.hSpcl
  hpR := td.hpR
  hRSm := td.hRSm
  hRSp := td.hRSp
  hRZ := td.hRZ
  hSmZ := td.hSmZ
  hSpZ := td.hSpZ
  hSmSp := td.hSmSp
  hdm_cont := by
    apply ContinuousOn.mul
    · exact continuousOn_const.mul td.hsm_cont
    · exact continuous_cornerCutoff.comp_continuousOn td.htm_cont
  hdp_cont := by
    apply continuousOn_const.sub
    apply ContinuousOn.mul
    · exact continuousOn_const.mul td.hsp_cont
    · exact continuous_cornerCutoff.comp_continuousOn td.htp_cont
  hdm_range := by
    intro x hx
    have hsm := td.hsm_mem x hx
    have hχnn := cornerCutoff_nonneg (td.tm x)
    have hχ1 := cornerCutoff_le_one (td.htm_nonneg x hx)
    have hεsm_nn : 0 ≤ td.ε * td.sm x := mul_nonneg td.hε.le hsm.1
    have hεsm_le : td.ε * td.sm x ≤ 1 := mul_le_one₀ td.hε1.le hsm.1 hsm.2
    refine ⟨mul_nonneg hεsm_nn hχnn, ?_⟩
    exact mul_le_one₀ hεsm_le hχnn hχ1
  hdp_range := by
    intro x hx
    have hsp := td.hsp_mem x hx
    have hχnn := cornerCutoff_nonneg (td.tp x)
    have hχ1 := cornerCutoff_le_one (td.htp_nonneg x hx)
    have hεsp_nn : 0 ≤ td.ε * td.sp x := mul_nonneg td.hε.le hsp.1
    have hεsp_le : td.ε * td.sp x ≤ 1 := mul_le_one₀ td.hε1.le hsp.1 hsp.2
    have hprod_nn : 0 ≤ td.ε * td.sp x * cornerCutoff (td.tp x) := mul_nonneg hεsp_nn hχnn
    have hprod_le : td.ε * td.sp x * cornerCutoff (td.tp x) ≤ 1 :=
      mul_le_one₀ hεsp_le hχnn hχ1
    exact ⟨by linarith, by linarith⟩
  hdm_R := by
    intro x hx
    rw [td.hsm_R x hx]; ring
  hdp_R := by
    intro x hx
    rw [td.hsp_R x hx]; ring
  hdm_CZ := by
    intro x hx
    obtain ⟨htm0, hγ⟩ := td.hCZm x hx
    rw [htm0, cornerCutoff_zero, mul_one]
    exact hγ
  hdp_CZ := by
    intro x hx
    obtain ⟨htp0, hγ⟩ := td.hCZp x hx
    rw [htp0, cornerCutoff_zero, mul_one]
    exact hγ
  hCZcover := td.hCZcover
  hcov := td.hcov
  hcovp := td.hcovp

/-- Existence form of `rayCollar_of_tubeData`. -/
theorem nonempty_rayCollar_of_tubeData {X : Type*} [TopologicalSpace X]
    {Z CZ : Set X} {γ : ℝ → X} {p : X} (td : TubeData X Z CZ γ p) :
    Nonempty (RayCollar X Z CZ γ p) :=
  ⟨rayCollar_of_tubeData td⟩

end Uniformization
