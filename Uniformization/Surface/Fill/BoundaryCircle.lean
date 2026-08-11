/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Push
import Uniformization.Surface.Fill.Collar

/-!
# Straightened boundary boxes (W7 step L5, boundary-structure layer)

This file opens the collar-bundle / boundary-structure layer that sits on top of
the straightening charts of `Push.lean`.  Working with the same hypotheses as
`exists_push_into` (open piece `V`, the local dichotomy `hdich`, the level
condition `hfc`, and the germ payload `hchart`), it produces, at each frontier
point `ξ`, a **straightened product box**: a maximal-atlas chart `ψ` in which the
collar coordinate `f` is exactly the real part, `V` is the `{c < re}` half of an
open rectangle, and — the new ingredient beyond `Push.lean` — the frontier `∂V`
is *exactly* the middle segment `{re = c}` of that rectangle.

## Deliverable D1 (`exists_straight_box`)

At `ξ ∈ frontier V` there are `ψ ∈ riemannAtlas X`, `ξ ∈ ψ.source`, half-widths
`δ, ε > 0`, and the box `B = {z | |re z − c| < δ ∧ |im z − im (ψ ξ)| < ε}`
inside `ψ.target` with, writing `W = ψ.symm '' B`:

* `(ψ ξ).re = c`, `W` open, `ξ ∈ W`;
* `f (ψ.symm z) = re z` for `z ∈ B`;
* `V ∩ W = ψ.symm '' {z ∈ B | c < re z}` (the `{re > c}` half);
* `frontier V ∩ W = ψ.symm '' {z ∈ B | re z = c}` (the middle segment).

The last equality is the new content.  Its `⊆` inclusion is `hfc`
(a frontier point has `f = c`, hence `re = c`); its `⊇` inclusion says every
`re = c` point of the box lies on the frontier: it is not in `V` (dichotomy,
`c < c` is false) and it is a limit of `{re > c}`-points, all of which are in `V`.
-/

open Set Metric Topology Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The product box in `ℂ` -/

/-- The open product box in `ℂ` around a center with real part `c` and imaginary
part `q.im`, of half-widths `δ` (real direction) and `ε` (imaginary direction). -/
def straightBox (q : ℂ) (c δ ε : ℝ) : Set ℂ :=
  {z : ℂ | |z.re - c| < δ ∧ |z.im - q.im| < ε}

@[simp] theorem mem_straightBox {q : ℂ} {c δ ε : ℝ} {z : ℂ} :
    z ∈ straightBox q c δ ε ↔ |z.re - c| < δ ∧ |z.im - q.im| < ε := Iff.rfl

theorem isOpen_straightBox (q : ℂ) (c δ ε : ℝ) : IsOpen (straightBox q c δ ε) := by
  rw [straightBox, Set.ofPred_and]
  exact (isOpen_lt ((Complex.continuous_re.sub continuous_const).abs) continuous_const).inter
    (isOpen_lt ((Complex.continuous_im.sub continuous_const).abs) continuous_const)

private theorem norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]

/-- A box with half-widths `δ, ε` around a point of real part `c` sits inside the
ball of radius `δ + ε`. -/
theorem straightBox_subset_ball {q : ℂ} {c δ ε : ℝ} (hqre : q.re = c) :
    straightBox q c δ ε ⊆ Metric.ball q (δ + ε) := by
  intro z hz
  rw [mem_straightBox] at hz
  rw [Metric.mem_ball, dist_eq_norm]
  have h := norm_le_abs_re_add_abs_im (z - q)
  rw [Complex.sub_re, Complex.sub_im, hqre] at h
  linarith [hz.1, hz.2]

/-! ## D1 — straightened chart keeping atlas membership -/

/-- **Straightening chart at a frontier point (atlas form).**  As
`Push.exists_chart_at`, but additionally exposing `ψ ∈ riemannAtlas X`, which the
boundary-structure layer needs to relate different charts.  The proof mirrors
`exists_chart_at` (built on `exists_biholo_chart_germ`). -/
theorem exists_straight_chart [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {ξ : X} (hξ : ξ ∈ frontier V) :
    ∃ (ψ : OpenPartialHomeomorph X ℂ) (ρ : ℝ), ψ ∈ riemannAtlas X ∧
      0 < ρ ∧ ξ ∈ ψ.source ∧
      Metric.ball (ψ ξ) ρ ⊆ ψ.target ∧
      (∀ x ∈ ψ.symm '' Metric.ball (ψ ξ) ρ, (ψ x).re = f x) ∧
      (∀ x ∈ ψ.symm '' Metric.ball (ψ ξ) ρ, (x ∈ V ↔ c < f x)) := by
  obtain ⟨e, he, hξe, F, hFan, hpayload, hderiv⟩ := hchart ξ hξ
  obtain ⟨ψ, hψ, hξψ, hψsrc, hψeq⟩ := exists_biholo_chart_germ he hξe hFan hderiv
  have hψH : ∀ᶠ x in 𝓝 ξ, (ψ x).re = f x := by
    have hpb : ∀ᶠ x in 𝓝 ξ, (F (e x)).re = f (e.symm (e x)) :=
      (e.continuousAt hξe).eventually hpayload
    filter_upwards [hpb, e.open_source.mem_nhds hξe, ψ.open_source.mem_nhds hξψ]
      with x hx hxe hxψ
    rw [hψeq x hxψ, hx, e.left_inv hxe]
  have hdd : ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x) := hdich ξ hξ
  set q := ψ ξ with hq
  have hqtgt : q ∈ ψ.target := ψ.map_source hξψ
  have hsymmq : ψ.symm q = ξ := ψ.left_inv hξψ
  have hOnhds : {x | (ψ x).re = f x} ∩ ψ.source ∩ {x | x ∈ V ↔ c < f x} ∈ 𝓝 ξ :=
    inter_mem (inter_mem hψH (ψ.open_source.mem_nhds hξψ)) hdd
  obtain ⟨O₀, hO₀sub, hO₀o, hξO₀⟩ := _root_.mem_nhds_iff.mp hOnhds
  have hpre : ψ.symm ⁻¹' O₀ ∩ ψ.target ∈ 𝓝 q :=
    inter_mem ((ψ.continuousAt_symm hqtgt).preimage_mem_nhds
      (by rw [hsymmq]; exact hO₀o.mem_nhds hξO₀)) (ψ.open_target.mem_nhds hqtgt)
  obtain ⟨ρ, hρpos, hballρ⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ψ, ρ, hψ, hρpos, hξψ, fun w hw => (hballρ hw).2, ?_, ?_⟩
  · rintro x ⟨w, hw, rfl⟩
    exact (hO₀sub ((hballρ hw).1)).1.1
  · rintro x ⟨w, hw, rfl⟩
    exact (hO₀sub ((hballρ hw).1)).2

/-- **D1 — straightened product box at a frontier point.**  Under the collar
hypotheses (`hVo` open, `hdich` the local dichotomy, `hfc` the level, `hchart`
the germ payload), each frontier point `ξ` carries a maximal-atlas chart `ψ` and
an open box `B = straightBox (ψ ξ) c δ ε ⊆ ψ.target` on which:

* `(ψ ξ).re = c`, `W := ψ.symm '' B` is open with `ξ ∈ W`;
* `f (ψ.symm z) = z.re` for `z ∈ B`;
* `V ∩ W` is the `{re > c}` half of `W`;
* `frontier V ∩ W` is exactly the middle segment `{re = c}` of `W`.
-/
theorem exists_straight_box [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {ξ : X} (hξ : ξ ∈ frontier V) :
    ∃ (ψ : OpenPartialHomeomorph X ℂ) (δ ε : ℝ), ψ ∈ riemannAtlas X ∧
      ξ ∈ ψ.source ∧ 0 < δ ∧ 0 < ε ∧ (ψ ξ).re = c ∧
      straightBox (ψ ξ) c δ ε ⊆ ψ.target ∧
      IsOpen (ψ.symm '' straightBox (ψ ξ) c δ ε) ∧
      ξ ∈ ψ.symm '' straightBox (ψ ξ) c δ ε ∧
      (∀ z ∈ straightBox (ψ ξ) c δ ε, f (ψ.symm z) = z.re) ∧
      V ∩ ψ.symm '' straightBox (ψ ξ) c δ ε
        = ψ.symm '' {z ∈ straightBox (ψ ξ) c δ ε | c < z.re} ∧
      frontier V ∩ ψ.symm '' straightBox (ψ ξ) c δ ε
        = ψ.symm '' {z ∈ straightBox (ψ ξ) c δ ε | z.re = c} := by
  obtain ⟨ψ, ρ, hψ, hρ, hξψ, hball, hWre, hWdich⟩ := exists_straight_chart hdich hchart hξ
  set q := ψ ξ with hq
  -- `q.re = c`
  have hξimg : ξ ∈ ψ.symm '' Metric.ball q ρ := ⟨q, mem_ball_self hρ, ψ.left_inv hξψ⟩
  have hqre : q.re = c := by
    have h := hWre ξ hξimg
    rw [h, hfc ξ hξ]
  -- the box (half-widths `ρ/2` each)
  set δ := ρ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  set box := straightBox q c δ δ with hbox_def
  have hboxopen : IsOpen box := by rw [hbox_def]; exact isOpen_straightBox q c δ δ
  have hbox_ball : box ⊆ Metric.ball q ρ := by
    have := straightBox_subset_ball (q := q) (c := c) (δ := δ) (ε := δ) hqre
    rw [show δ + δ = ρ by rw [hδ]; ring] at this
    exact hbox_def ▸ this
  have hbox_tgt : box ⊆ ψ.target := hbox_ball.trans hball
  -- pointwise facts on the box
  have himg : ∀ z ∈ box, ψ.symm z ∈ ψ.symm '' Metric.ball q ρ :=
    fun z hz => ⟨z, hbox_ball hz, rfl⟩
  have hf_eq : ∀ z ∈ box, f (ψ.symm z) = z.re := by
    intro z hz
    have h := hWre (ψ.symm z) (himg z hz)
    rw [ψ.right_inv (hbox_tgt hz)] at h
    exact h.symm
  have hdich_box : ∀ z ∈ box, (ψ.symm z ∈ V ↔ c < z.re) := by
    intro z hz
    have h := hWdich (ψ.symm z) (himg z hz)
    rw [hf_eq z hz] at h
    exact h
  -- `W` open, `ξ ∈ W`
  have hWopen : IsOpen (ψ.symm '' box) :=
    ψ.symm.isOpen_image_of_subset_source hboxopen
      (by rw [OpenPartialHomeomorph.symm_source]; exact hbox_tgt)
  have hqbox : q ∈ box := by
    rw [hbox_def, mem_straightBox]
    exact ⟨by rw [hqre, sub_self, abs_zero]; exact hδpos,
      by rw [sub_self, abs_zero]; exact hδpos⟩
  have hξW : ξ ∈ ψ.symm '' box := ⟨q, hqbox, ψ.left_inv hξψ⟩
  -- the V-side set `Sp`
  set Sp := {z ∈ box | c < z.re} with hSp_def
  have hSpV : ψ.symm '' Sp ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hdich_box z hz.1).mpr hz.2
  -- limit lemma: every `re = c` point of the box is a limit of `Sp`-points
  have hmem_closure : ∀ z ∈ box, z.re = c → z ∈ closure Sp := by
    intro z hzbox hzrec
    rw [_root_.mem_closure_iff]
    intro O hO hzO
    have hcont : ContinuousAt (fun t : ℝ => z + (t : ℂ)) 0 := by fun_prop
    have hz_mem : (fun t : ℝ => z + (t : ℂ)) 0 ∈ O ∩ box := by
      simp only [Complex.ofReal_zero, add_zero]; exact ⟨hzO, hzbox⟩
    have hev : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), (z + (t : ℂ)) ∈ O ∩ box :=
      hcont.preimage_mem_nhds ((hO.inter hboxopen).mem_nhds hz_mem)
    have hev' : ∀ᶠ (t : ℝ) in 𝓝[>] (0 : ℝ), (z + (t : ℂ)) ∈ O ∩ box :=
      hev.filter_mono nhdsWithin_le_nhds
    obtain ⟨t, htmem, htpos⟩ := (hev'.and self_mem_nhdsWithin).exists
    have hre : c < (z + (t : ℂ)).re := by
      rw [Complex.add_re, Complex.ofReal_re, hzrec]
      exact lt_add_of_pos_right c htpos
    exact ⟨z + (t : ℂ), htmem.1, ⟨htmem.2, hre⟩⟩
  refine ⟨ψ, δ, δ, hψ, hξψ, hδpos, hδpos, hqre, hbox_tgt, hWopen, hξW,
    hf_eq, ?_, ?_⟩
  · -- `V ∩ W = ψ.symm '' Sp`
    apply Subset.antisymm
    · rintro x ⟨hxV, z, hzbox, rfl⟩
      exact ⟨z, ⟨hzbox, (hdich_box z hzbox).mp hxV⟩, rfl⟩
    · rintro _ ⟨z, ⟨hzbox, hzlt⟩, rfl⟩
      exact ⟨(hdich_box z hzbox).mpr hzlt, z, hzbox, rfl⟩
  · -- `frontier V ∩ W = ψ.symm '' {re = c}`
    apply Subset.antisymm
    · rintro x ⟨hxfr, z, hzbox, rfl⟩
      have hzrec : z.re = c := by rw [← hf_eq z hzbox]; exact hfc (ψ.symm z) hxfr
      exact ⟨z, ⟨hzbox, hzrec⟩, rfl⟩
    · rintro _ ⟨z, ⟨hzbox, hzrec⟩, rfl⟩
      refine ⟨?_, ⟨z, hzbox, rfl⟩⟩
      rw [hVo.frontier_eq]
      constructor
      · -- `ψ.symm z ∈ closure V`
        have hcw : ContinuousWithinAt ψ.symm Sp z :=
          (ψ.continuousAt_symm (hbox_tgt hzbox)).continuousWithinAt
        exact closure_mono hSpV (hcw.mem_closure_image (hmem_closure z hzbox hzrec))
      · -- `ψ.symm z ∉ V`
        intro hv
        have := (hdich_box z hzbox).mp hv
        rw [hzrec] at this
        exact lt_irrefl c this

/-! ## D2 infrastructure — the real part is the transition-invariant coordinate -/

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- On a straightening chart, the real part of `ψ x` recovers the collar
coordinate `f x` for every `x` in the box image `ψ.symm '' B`.  (Corollary of the
box property `f (ψ.symm z) = z.re`.) -/
theorem re_eq_f_of_mem_boxImage {f : X → ℝ} {ψ : OpenPartialHomeomorph X ℂ} {B : Set ℂ}
    (hBtgt : B ⊆ ψ.target) (hf : ∀ z ∈ B, f (ψ.symm z) = z.re)
    {x : X} (hx : x ∈ ψ.symm '' B) : (ψ x).re = f x := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [ψ.right_inv (hBtgt hz)]
  exact (hf z hz).symm

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **Transitions preserve the real part.**  On the overlap of two straightening
charts (each with `Re ∘ chart = f` on its box image) the transition
`ψ₂ ∘ ψ₁.symm` preserves the real part: both real parts equal the common collar
coordinate `f` at the surface point.  This is the key rigidity that pins the two
boundary arcs together in the circle chain of D2. -/
theorem re_transition_eq {f : X → ℝ}
    {ψ₁ ψ₂ : OpenPartialHomeomorph X ℂ} {B₁ B₂ : Set ℂ}
    (hB₁tgt : B₁ ⊆ ψ₁.target) (hf₁ : ∀ z ∈ B₁, f (ψ₁.symm z) = z.re)
    (hB₂tgt : B₂ ⊆ ψ₂.target) (hf₂ : ∀ z ∈ B₂, f (ψ₂.symm z) = z.re)
    {x : X} (hx₁ : x ∈ ψ₁.symm '' B₁) (hx₂ : x ∈ ψ₂.symm '' B₂) :
    (ψ₁ x).re = (ψ₂ x).re := by
  rw [re_eq_f_of_mem_boxImage hB₁tgt hf₁ hx₁, re_eq_f_of_mem_boxImage hB₂tgt hf₂ hx₂]

end Uniformization
