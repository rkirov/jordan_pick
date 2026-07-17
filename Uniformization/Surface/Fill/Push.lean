/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Collar
import Uniformization.Surface.Fill.Retraction

/-!
# Open ↔ closed transfer for a level-curve piece (W7 step L5.6)

The delivered `exists_level_piece_regular_frontier` (`LevelChart.lean`) equips the
piece `V` with a harmonic collar coordinate `f`, a level `c`, and, at every
frontier point `ξ`, a *straightening chart* germ `(e, F)` with `Re (F ∘ e) = f`
near `ξ` and nonvanishing derivative, together with the local dichotomy
`x ∈ V ↔ c < f x`.  This file performs the last surface-topology step of the
harmonic (F3) route:

> if `closure V` is simply connected, then so is the open piece `V`.

## Strategy (inward push)

The key tool is the **inward push** `exists_push_into`: for every compact
`L ⊆ V` there is a continuous self-map `g : X → X` that is the identity on `L`
and pushes all of `closure V` into `V`.  It is built as a finite composition of
per-chart pushes: in each straightening chart `ψᵢ` (where `f = Re ψᵢ`) the map
increases the real coordinate by a bump-modulated deficit, moving frontier
points (where `Re ψᵢ = c`) strictly into `{c < Re ψᵢ} = V`, while leaving points
already deep inside `V` (in particular all of `L`, once the push amount is chosen
small enough) fixed.  A finite subcover of the compact `frontier V` by chart
cores makes the composition land every closure point in `V`.

Given `g`, the transfer is the retract argument specialised to a loop's compact
image: a loop `p` in `V` is null-homotopic in the simply connected `closure V`;
post-composing that null-homotopy with a `g` fixing `range p` yields a
null-homotopy *inside* `V` (`isSimplyConnected_iff_exists_homotopy_refl_forall_mem`,
as in `Retraction.lean`).  Path-connectivity of `V` is obtained the same way.

`exists_push_into` is public (F3.c may reuse it) and the transfer theorem is
`isSimplyConnected_of_closure`.
-/

open Set Metric Topology Filter

namespace Uniformization

/-! ## The complex push -/

noncomputable section PushDefs
variable (q : ℂ) (ρ δ c : ℝ)

/-- A radial bump on `ℂ`: `1` on `closedBall q (ρ/4)`, `0` off `ball q (ρ/2)`. -/
def bump (z : ℂ) : ℝ := max 0 (min 1 ((ρ - 2 * dist z q) * (2 / ρ)))
/-- The (clamped) real-part deficit at `z` relative to the level `c` and margin `δ`. -/
def defic (z : ℂ) : ℝ := max 0 (min δ (c + δ - z.re))
/-- Push `z` in the positive real direction by a bump-modulated deficit. -/
def pushz (z : ℂ) : ℂ := z + ((bump q ρ z * defic δ c z : ℝ) : ℂ)

variable {q ρ δ c}

theorem bump_nonneg (z : ℂ) : 0 ≤ bump q ρ z := le_max_left _ _
theorem bump_le_one (z : ℂ) : bump q ρ z ≤ 1 := max_le (by norm_num) (min_le_left _ _)
theorem defic_nonneg (z : ℂ) : 0 ≤ defic δ c z := le_max_left _ _
theorem defic_le (hδ : 0 ≤ δ) (z : ℂ) : defic δ c z ≤ δ := max_le hδ (min_le_left _ _)

theorem continuous_bump (hρ : 0 < ρ) : Continuous (bump q ρ) :=
  continuous_const.max (continuous_const.min ((continuous_const.sub
    (continuous_const.mul (continuous_id.dist continuous_const))).mul continuous_const))
theorem continuous_defic : Continuous (defic δ c) :=
  continuous_const.max (continuous_const.min (continuous_const.sub Complex.continuous_re))
theorem continuous_pushz (hρ : 0 < ρ) : Continuous (pushz q ρ δ c) :=
  continuous_id.add (Complex.continuous_ofReal.comp ((continuous_bump hρ).mul continuous_defic))

theorem pushz_re (z : ℂ) : (pushz q ρ δ c z).re = z.re + bump q ρ z * defic δ c z := by
  simp [pushz]

theorem bump_eq_one (hρ : 0 < ρ) {z : ℂ} (hz : dist z q ≤ ρ/4) : bump q ρ z = 1 := by
  have hexp : (ρ - 2 * dist z q) * (2 / ρ) = (2*ρ - 4 * dist z q)/ρ := by field_simp; ring
  have h2 : 1 ≤ (ρ - 2 * dist z q) * (2 / ρ) := by rw [hexp, le_div_iff₀ hρ]; linarith
  rw [bump, min_eq_left h2, max_eq_right (by norm_num)]

theorem bump_eq_zero (hρ : 0 < ρ) {z : ℂ} (hz : ρ/2 ≤ dist z q) : bump q ρ z = 0 := by
  have hle : (ρ - 2 * dist z q) * (2 / ρ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [bump, min_eq_right (hle.trans zero_le_one), max_eq_left hle]

theorem defic_eq_delta (hδ : 0 < δ) {z : ℂ} (hz : z.re ≤ c) : defic δ c z = δ := by
  rw [defic, min_eq_left (by linarith), max_eq_right hδ.le]

theorem defic_eq_zero (hδ : 0 ≤ δ) {z : ℂ} (hz : c + δ ≤ z.re) : defic δ c z = 0 := by
  have hle : c + δ - z.re ≤ 0 := by linarith
  rw [defic, min_eq_right (hle.trans hδ), max_eq_left hle]

theorem pushz_mem_ball (hρ : 0 < ρ) (hδ : 0 < δ) (hδρ : δ ≤ ρ/2) {z : ℂ}
    (hz : z ∈ ball q ρ) : pushz q ρ δ c z ∈ ball q ρ := by
  have hdisp : dist (pushz q ρ δ c z) z = bump q ρ z * defic δ c z := by
    rw [dist_eq_norm, show pushz q ρ δ c z - z = ((bump q ρ z * defic δ c z : ℝ):ℂ) from by
      rw [pushz]; ring, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (bump_nonneg z) (defic_nonneg z))]
  rw [mem_ball]
  by_cases hd : ρ/2 ≤ dist z q
  · rw [pushz, bump_eq_zero hρ hd]; simpa using (mem_ball.mp hz)
  · push_neg at hd
    have hb : bump q ρ z * defic δ c z ≤ δ :=
      le_trans (mul_le_mul (bump_le_one z) (defic_le hδ.le z) (defic_nonneg z) (by norm_num))
        (le_of_eq (one_mul δ))
    calc dist (pushz q ρ δ c z) q ≤ dist (pushz q ρ δ c z) z + dist z q := dist_triangle _ _ _
      _ = bump q ρ z * defic δ c z + dist z q := by rw [hdisp]
      _ ≤ δ + dist z q := by linarith
      _ < ρ := by linarith

end PushDefs

/-! ## Abstract composition of pushes -/

section Composition
variable {X : Type*} [TopologicalSpace X]

/-- Fold a list of continuous self-maps into a composite that applies the head
first, then the rest. -/
def compList (l : List (C(X, X) × Set X)) : C(X, X) :=
  l.foldr (fun p acc => acc.comp p.1) (ContinuousMap.id X)

@[simp] theorem compList_nil_apply (x : X) :
    compList ([] : List (C(X, X) × Set X)) x = x := rfl

theorem compList_cons (p : C(X, X) × Set X) (l : List (C(X, X) × Set X)) (x : X) :
    compList (p :: l) x = compList l (p.1 x) := rfl

/-- **Composition of inward pushes.**  A list of continuous maps, each
`V`-preserving (`h1`), each moving a frontier point to itself or into `V`
(`h2`), each pushing a frontier point of its associated "core" `p.2` into `V`
(`h4`), and each fixing `L` (`h3`), whose cores cover `frontier V` (`hcov`),
composes to a single map sending all of `closure V` into `V` and fixing `L`. -/
theorem exists_comp_push {V L : Set X} (hVo : IsOpen V)
    (l : List (C(X, X) × Set X))
    (h1 : ∀ p ∈ l, ∀ x ∈ V, p.1 x ∈ V)
    (h2 : ∀ p ∈ l, ∀ x ∈ frontier V, p.1 x = x ∨ p.1 x ∈ V)
    (h4 : ∀ p ∈ l, ∀ x ∈ frontier V ∩ p.2, p.1 x ∈ V)
    (h3 : ∀ p ∈ l, ∀ x ∈ L, p.1 x = x)
    (hcov : frontier V ⊆ ⋃ p ∈ l, p.2) :
    (∀ x ∈ closure V, compList l x ∈ V) ∧ (∀ x ∈ L, compList l x = x) := by
  have hUF : V ∪ frontier V = closure V := by
    rw [hVo.frontier_eq]; exact Set.union_sdiff_cancel subset_closure
  have hfrnV : ∀ x ∈ frontier V, x ∉ V := by
    intro x hx; rw [hVo.frontier_eq] at hx; exact hx.2
  have Qinv : ∀ (l : List (C(X, X) × Set X)),
      (∀ p ∈ l, ∀ x ∈ V, p.1 x ∈ V) →
      (∀ p ∈ l, ∀ x ∈ frontier V, p.1 x = x ∨ p.1 x ∈ V) →
      (∀ p ∈ l, ∀ x ∈ frontier V ∩ p.2, p.1 x ∈ V) →
      ∀ x ∈ closure V, (x ∈ V → compList l x ∈ V) ∧
        (x ∈ frontier V → compList l x ∈ V ∨ (compList l x = x ∧ ∀ p ∈ l, x ∉ p.2)) := by
    intro l
    induction l with
    | nil =>
      intro _ _ _ x _
      exact ⟨fun hx => by simpa using hx, fun _ => Or.inr ⟨by simp, by simp⟩⟩
    | cons p l ih =>
      intro h1 h2 h4 x hx
      have h1' := fun q hq => h1 q (List.mem_cons_of_mem _ hq)
      have h2' := fun q hq => h2 q (List.mem_cons_of_mem _ hq)
      have h4' := fun q hq => h4 q (List.mem_cons_of_mem _ hq)
      have hpx_cl : p.1 x ∈ closure V := by
        rw [← hUF] at hx ⊢
        rcases hx with hxV | hxF
        · exact Or.inl (h1 p (List.mem_cons_self ..) x hxV)
        · rcases h2 p (List.mem_cons_self ..) x hxF with he | hv
          · rw [he]; exact Or.inr hxF
          · exact Or.inl hv
      have IHres := ih h1' h2' h4' (p.1 x) hpx_cl
      refine ⟨fun hxV => ?_, fun hxF => ?_⟩
      · rw [compList_cons]; exact IHres.1 (h1 p (List.mem_cons_self ..) x hxV)
      · rw [compList_cons]
        rcases h2 p (List.mem_cons_self ..) x hxF with he | hv
        · have hFpx : p.1 x ∈ frontier V := by rw [he]; exact hxF
          rcases IHres.2 hFpx with hin | ⟨heq, hnot⟩
          · exact Or.inl hin
          · refine Or.inr ⟨by rw [heq, he], fun q hq => ?_⟩
            rcases List.mem_cons.mp hq with heqp | hq'
            · rw [heqp]
              intro hxp2
              have hv : p.1 x ∈ V := h4 p (List.mem_cons_self ..) x ⟨hxF, hxp2⟩
              rw [he] at hv; exact hfrnV x hxF hv
            · have := hnot q hq'; rwa [he] at this
        · exact Or.inl (IHres.1 hv)
  have hmain := Qinv l h1 h2 h4
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [← hUF] at hx
    rcases hx with hxV | hxF
    · exact (hmain x (hUF ▸ subset_closure hxV)).1 hxV
    · have hxcl : x ∈ closure V := hUF ▸ (Or.inr hxF)
      rcases (hmain x hxcl).2 hxF with hin | ⟨_, hnot⟩
      · exact hin
      · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hcov hxF)
        exact absurd hxp (hnot p hp)
  · have aux : ∀ (l : List (C(X, X) × Set X)), (∀ p ∈ l, ∀ x ∈ L, p.1 x = x) →
        ∀ x ∈ L, compList l x = x := by
      intro l
      induction l with
      | nil => intro _ x _; rfl
      | cons p l ih =>
        intro h3 x hxL
        rw [compList_cons, h3 p (List.mem_cons_self ..) x hxL]
        exact ih (fun q hq => h3 q (List.mem_cons_of_mem _ hq)) x hxL
    exact aux l h3

/-- **Loop transport across a push.**  If `g` sends `closure V` into `V` and
fixes the loop `p`, then any null-homotopy of `p` valued in `closure V`
post-composes with `g` to a null-homotopy valued in `V`. -/
theorem exists_homotopy_refl_in_of_push {V : Set X} (g : C(X, X))
    (hgV : ∀ y ∈ closure V, g y ∈ V) {x : X} (p : Path x x)
    (hgid : ∀ t, g (p t) = p t) (H : p.Homotopy (Path.refl x)) (hH : ∀ st, H st ∈ closure V) :
    ∃ F : p.Homotopy (Path.refl x), ∀ st, F st ∈ V := by
  refine ⟨{
    toFun := fun st => g (H st)
    continuous_toFun := g.continuous.comp H.continuous
    map_zero_left := fun t => by
      show g (H (0, t)) = p t
      rw [H.apply_zero t]; exact hgid t
    map_one_left := fun t => by
      show g (H (1, t)) = (Path.refl x) t
      rw [H.apply_one t, Path.refl_apply]
      have h := hgid 0
      rwa [show p 0 = x from p.source'] at h
    prop' := fun t s hs => by
      show g (H (t, s)) = p.toContinuousMap s
      rw [H.eq_fst t hs]; exact hgid s }, ?_⟩
  intro st
  exact hgV _ (hH st)

end Composition

/-! ## Per-chart push and the transfer -/

section Chart
open Rado
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Per-chart inward push.**  In a straightening chart `ψ` (with `Re ψ = f`
and the dichotomy `x ∈ V ↔ c < f x` on the ball `ψ.symm '' ball (ψ ξ) ρ`), the
bump-modulated real-part push yields a continuous self-map `g` that preserves
`V`, sends each frontier point to itself or into `V`, pushes frontier points of
the core `ψ.symm '' ball (ψ ξ) (ρ/4)` into `V`, and moves a point only if it
lies in `ψ.symm '' closedBall (ψ ξ) (ρ/2)` with `f x < c + δ`. -/
theorem exists_push_of_chart [T2Space X] {V : Set X} (hVo : IsOpen V)
    {f : X → ℝ} {c : ℝ} (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    {ψ : OpenPartialHomeomorph X ℂ} {ξ : X} (hξs : ξ ∈ ψ.source)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hδρ : δ ≤ ρ/2)
    (hball : Metric.ball (ψ ξ) ρ ⊆ ψ.target)
    (hWre : ∀ x ∈ ψ.symm '' Metric.ball (ψ ξ) ρ, (ψ x).re = f x)
    (hWdich : ∀ x ∈ ψ.symm '' Metric.ball (ψ ξ) ρ, (x ∈ V ↔ c < f x)) :
    ∃ g : C(X, X),
      (∀ x ∈ V, g x ∈ V) ∧
      (∀ x ∈ frontier V, g x = x ∨ g x ∈ V) ∧
      (∀ x ∈ frontier V ∩ ψ.symm '' Metric.ball (ψ ξ) (ρ/4), g x ∈ V) ∧
      (∀ x, g x ≠ x → x ∈ ψ.symm '' Metric.closedBall (ψ ξ) (ρ/2) ∧ f x < c + δ) := by
  classical
  set q := ψ ξ with hq
  set W := ψ.symm '' Metric.ball q ρ with hW
  have hballtgt : Metric.ball q ρ ⊆ ψ.target := hball
  have hWsource : W ⊆ ψ.source := by
    rintro x ⟨w, hw, rfl⟩; exact ψ.map_target (hballtgt hw)
  have hWopen : IsOpen W := ψ.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (by rw [OpenPartialHomeomorph.symm_source]; exact hballtgt)
  have hWpsi : ∀ x ∈ W, ψ x ∈ Metric.ball q ρ := by
    rintro x ⟨w, hw, rfl⟩; rw [ψ.right_inv (hballtgt hw)]; exact hw
  have hWli : ∀ x ∈ W, ψ.symm (ψ x) = x := fun x hx => ψ.left_inv (hWsource hx)
  have hg1 : ∀ x ∈ W, ψ.symm (pushz q ρ δ c (ψ x)) ∈ W := fun x hx =>
    ⟨pushz q ρ δ c (ψ x), pushz_mem_ball hρ hδ hδρ (hWpsi x hx), rfl⟩
  have hfpush : ∀ x ∈ W, f (ψ.symm (pushz q ρ δ c (ψ x)))
      = f x + bump q ρ (ψ x) * defic δ c (ψ x) := by
    intro x hx
    have hp : pushz q ρ δ c (ψ x) ∈ Metric.ball q ρ := pushz_mem_ball hρ hδ hδρ (hWpsi x hx)
    have hre := hWre _ (hg1 x hx)
    rw [ψ.right_inv (hballtgt hp)] at hre
    rw [← hre, pushz_re, hWre x hx]
  set g₀ : X → X := fun x => if x ∈ W then ψ.symm (pushz q ρ δ c (ψ x)) else x with hg0
  set C := ψ.symm '' Metric.closedBall q (ρ/2) with hC
  have hcbtgt : Metric.closedBall q (ρ/2) ⊆ ψ.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hCW : C ⊆ W := by
    rw [hC, hW]; exact Set.image_mono (Metric.closedBall_subset_ball (by linarith))
  have hCcpt : IsCompact C :=
    (isCompact_closedBall q (ρ/2)).image_of_continuousOn (ψ.continuousOn_symm.mono hcbtgt)
  have hCclosed : IsClosed C := hCcpt.isClosed
  have hg0id : ∀ x, x ∉ C → g₀ x = x := by
    intro x hxC
    by_cases hxW : x ∈ W
    · have hnotcb : ψ x ∉ Metric.closedBall q (ρ/2) := fun hcb => hxC ⟨ψ x, hcb, hWli x hxW⟩
      have hd : ρ/2 ≤ dist (ψ x) q := by
        rw [Metric.mem_closedBall] at hnotcb; exact (not_le.mp hnotcb).le
      simp only [hg0, if_pos hxW]; rw [pushz, bump_eq_zero hρ hd]; simp [hWli x hxW]
    · simp only [hg0, if_neg hxW]
  have hF1onW : ContinuousOn (fun x => ψ.symm (pushz q ρ δ c (ψ x))) W := by
    have hψW : ContinuousOn ψ W := ψ.continuousOn.mono hWsource
    have hpush : ContinuousOn (fun x => pushz q ρ δ c (ψ x)) W :=
      (continuous_pushz hρ).comp_continuousOn hψW
    have hmaps : Set.MapsTo (fun x => pushz q ρ δ c (ψ x)) W (Metric.ball q ρ) :=
      fun x hx => pushz_mem_ball hρ hδ hδρ (hWpsi x hx)
    exact (ψ.continuousOn_symm.mono hball).comp hpush hmaps
  have hg0cont : Continuous g₀ := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · have heq : g₀ =ᶠ[nhds x] (fun y => ψ.symm (pushz q ρ δ c (ψ y))) := by
        filter_upwards [hWopen.mem_nhds hx] with y hy; simp only [hg0, if_pos hy]
      exact (hF1onW.continuousAt (hWopen.mem_nhds hx)).congr heq.symm
    · have hxC : x ∈ Cᶜ := fun h => hx (hCW h)
      have heq : g₀ =ᶠ[nhds x] id := by
        filter_upwards [hCclosed.isOpen_compl.mem_nhds hxC] with y hy; exact hg0id y hy
      exact continuousAt_id.congr heq.symm
  refine ⟨⟨g₀, hg0cont⟩, ?_, ?_, ?_, ?_⟩
  · intro x hxV
    by_cases hxW : x ∈ W
    · show g₀ x ∈ V
      simp only [hg0, if_pos hxW]
      rw [hWdich _ (hg1 x hxW), hfpush x hxW]
      have h1 : c < f x := (hWdich x hxW).mp hxV
      have h2 : 0 ≤ bump q ρ (ψ x) * defic δ c (ψ x) := mul_nonneg (bump_nonneg _) (defic_nonneg _)
      linarith
    · show g₀ x ∈ V; simp only [hg0, if_neg hxW]; exact hxV
  · intro x hxF
    by_cases hxW : x ∈ W
    · have hfxc : f x = c := hfc x hxF
      have hrexc : (ψ x).re = c := by rw [hWre x hxW, hfxc]
      by_cases hb : bump q ρ (ψ x) = 0
      · left; show g₀ x = x
        simp only [hg0, if_pos hxW]; rw [pushz, hb]; simp [hWli x hxW]
      · right; show g₀ x ∈ V
        simp only [hg0, if_pos hxW]
        rw [hWdich _ (hg1 x hxW), hfpush x hxW, hfxc, defic_eq_delta hδ (le_of_eq hrexc)]
        have hbpos : 0 < bump q ρ (ψ x) := lt_of_le_of_ne (bump_nonneg _) (Ne.symm hb)
        nlinarith
    · left; show g₀ x = x; simp only [hg0, if_neg hxW]
  · rintro x ⟨hxF, hxcore⟩
    have hxW : x ∈ W := by
      obtain ⟨w, hw, rfl⟩ := hxcore
      exact ⟨w, Metric.ball_subset_ball (by linarith) hw, rfl⟩
    show g₀ x ∈ V
    simp only [hg0, if_pos hxW]
    have hfxc : f x = c := hfc x hxF
    have hb1 : bump q ρ (ψ x) = 1 := by
      obtain ⟨w, hw, hwx⟩ := hxcore
      have hxw : ψ x = w := by
        rw [← hwx, ψ.right_inv (hcbtgt (Metric.ball_subset_closedBall
          (Metric.ball_subset_ball (by linarith) hw)))]
      rw [hxw]; exact bump_eq_one hρ (le_of_lt (Metric.mem_ball.mp hw))
    have hrexc : (ψ x).re = c := by rw [hWre x hxW, hfxc]
    rw [hWdich _ (hg1 x hxW), hfpush x hxW, hfxc, hb1, defic_eq_delta hδ (le_of_eq hrexc)]
    linarith
  · intro x hne
    by_cases hxW : x ∈ W
    · have hneq : pushz q ρ δ c (ψ x) ≠ ψ x := by
        intro h; apply hne; show g₀ x = x
        simp only [hg0, if_pos hxW, h]; exact hWli x hxW
      have hbd : bump q ρ (ψ x) * defic δ c (ψ x) ≠ 0 := by
        intro h; apply hneq; rw [pushz, h]; simp
      have hbne : bump q ρ (ψ x) ≠ 0 := fun h => hbd (by rw [h]; ring)
      have hdne : defic δ c (ψ x) ≠ 0 := fun h => hbd (by rw [h]; ring)
      refine ⟨?_, ?_⟩
      · have hd : dist (ψ x) q < ρ/2 := by
          by_contra hc; exact hbne (bump_eq_zero hρ (not_lt.mp hc))
        exact ⟨ψ x, Metric.mem_closedBall.mpr (le_of_lt hd), hWli x hxW⟩
      · have hre : (ψ x).re < c + δ := by
          by_contra hc; exact hdne (defic_eq_zero hδ.le (not_lt.mp hc))
        rw [← hWre x hxW]; exact hre
    · exact absurd (show g₀ x = x by simp only [hg0, if_neg hxW]) hne

/-- **Straightening chart at a frontier point.**  From the germ payload
(`hchart`) and the local dichotomy (`hdich`), each frontier point `ξ` acquires a
maximal-atlas chart `ψ` and radius `ρ` with `Re ψ = f` and the dichotomy holding
*pointwise* on the ball `ψ.symm '' ball (ψ ξ) ρ`. -/
theorem exists_chart_at [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {ξ : X} (hξ : ξ ∈ frontier V) :
    ∃ (ψ : OpenPartialHomeomorph X ℂ) (ρ : ℝ), 0 < ρ ∧ ξ ∈ ψ.source ∧
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
  refine ⟨ψ, ρ, hρpos, hξψ, fun w hw => (hballρ hw).2, ?_, ?_⟩
  · rintro x ⟨w, hw, rfl⟩
    exact (hO₀sub ((hballρ hw).1)).1.1
  · rintro x ⟨w, hw, rfl⟩
    exact (hO₀sub ((hballρ hw).1)).2

/-- **Margin selection.**  For a fixed straightening chart and a compact
`L ⊆ V`, there is a positive push amount `d ≤ ρ/2` small enough that no point of
`L` inside the chart core `closedBall (ψ ξ) (ρ/2)` is within `d` of the level
`c`; the push therefore fixes `L`. -/
theorem exists_delta_at [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ}
    {ψ : OpenPartialHomeomorph X ℂ} {ξ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (ψ ξ) ρ ⊆ ψ.target)
    (hWre : ∀ x ∈ ψ.symm '' Metric.ball (ψ ξ) ρ, (ψ x).re = f x)
    (hWdich : ∀ x ∈ ψ.symm '' Metric.ball (ψ ξ) ρ, (x ∈ V ↔ c < f x))
    {L : Set X} (hL : IsCompact L) (hLV : L ⊆ V) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ/2 ∧
      ∀ x ∈ L ∩ ψ.symm '' Metric.closedBall (ψ ξ) (ρ/2), c + d ≤ f x := by
  classical
  set q := ψ ξ with hq
  set Cset := ψ.symm '' Metric.closedBall q (ρ/2) with hCset
  have hcbtgt : Metric.closedBall q (ρ/2) ⊆ ψ.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hCsub : Cset ⊆ ψ.symm '' Metric.ball q ρ :=
    Set.image_mono (Metric.closedBall_subset_ball (by linarith))
  have hCsource : Cset ⊆ ψ.source := by
    rintro x ⟨w, hw, rfl⟩; exact ψ.map_target (hcbtgt hw)
  have hCcpt : IsCompact Cset :=
    (isCompact_closedBall q (ρ/2)).image_of_continuousOn (ψ.continuousOn_symm.mono hcbtgt)
  have hfC : ContinuousOn f Cset :=
    (Complex.continuous_re.comp_continuousOn (ψ.continuousOn.mono hCsource)).congr
      (fun x hx => (hWre x (hCsub hx)).symm)
  have hLCcpt : IsCompact (L ∩ Cset) := hL.inter_right hCcpt.isClosed
  by_cases hne : (L ∩ Cset).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hLCcpt.exists_isMinOn hne (hfC.mono inter_subset_right)
    have hx₀V : x₀ ∈ V := hLV hx₀.1
    have hlt : c < f x₀ := (hWdich x₀ (hCsub hx₀.2)).mp hx₀V
    refine ⟨min (f x₀ - c) (ρ/2), lt_min (by linarith) (by linarith), min_le_right _ _, ?_⟩
    intro x hx
    have hle : f x₀ ≤ f x := isMinOn_iff.mp hmin x hx
    have : min (f x₀ - c) (ρ/2) ≤ f x₀ - c := min_le_left _ _
    linarith
  · exact ⟨ρ/2, by linarith, le_refl _, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- **Inward push into a level piece.**  For every compact `L ⊆ V` there is a
continuous self-map `g : X → X` that fixes `L` pointwise and sends all of
`closure V` into `V`.  Built as a finite composition of per-chart pushes over a
finite subcover of the compact `frontier V`. -/
theorem exists_push_into [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ}
    (hVo : IsOpen V) (hVcl : IsCompact (closure V))
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {L : Set X} (hL : IsCompact L) (hLV : L ⊆ V) :
    ∃ g : C(X, X), (∀ x ∈ closure V, g x ∈ V) ∧ (∀ x ∈ L, g x = x) := by
  classical
  rcases eq_empty_or_nonempty (frontier V) with hfrE | hfrNE
  · -- no frontier: `closure V = V`, identity works
    have hcV : closure V = V := by
      have h : V ∪ frontier V = closure V := by
        rw [hVo.frontier_eq]; exact Set.union_sdiff_cancel subset_closure
      rw [← h, hfrE, union_empty]
    exact ⟨ContinuousMap.id X, fun x hx => by rw [hcV] at hx; exact hx, fun x _ => rfl⟩
  have hfrcpt : IsCompact (frontier V) :=
    hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  -- a nonempty chart type (needed so the chart-choosing function is total)
  obtain ⟨ξ₀, hξ₀⟩ := hfrNE
  obtain ⟨e₀, -, -⟩ := hchart ξ₀ hξ₀
  haveI : Nonempty (OpenPartialHomeomorph X ℂ) := ⟨e₀⟩
  -- per-point chart data
  choose! ch rho hpos hsrc hbl hWre hWdich using
    fun ξ (hξ : ξ ∈ frontier V) => exists_chart_at hdich hchart hξ
  set core := fun ξ => (ch ξ).symm '' Metric.ball ((ch ξ) ξ) (rho ξ / 4) with hcore
  have hcoreO : ∀ ξ ∈ frontier V, IsOpen (core ξ) := by
    intro ξ hξ
    exact (ch ξ).symm.isOpen_image_of_subset_source Metric.isOpen_ball
      (by rw [OpenPartialHomeomorph.symm_source]
          exact (Metric.ball_subset_ball (by linarith [hpos ξ hξ])).trans (hbl ξ hξ))
  have hξcore : ∀ ξ ∈ frontier V, ξ ∈ core ξ := fun ξ hξ =>
    ⟨(ch ξ) ξ, Metric.mem_ball_self (by linarith [hpos ξ hξ]), (ch ξ).left_inv (hsrc ξ hξ)⟩
  -- finite subcover of the compact frontier
  obtain ⟨t, htsub, htfin, htcov⟩ := hfrcpt.elim_finite_subcover_image hcoreO
    (fun ξ hξ => Set.mem_biUnion hξ (hξcore ξ hξ))
  -- margin data
  choose! dfun hdpos hdle hdgap using
    fun ξ (hξ : ξ ∈ frontier V) => exists_delta_at (hpos ξ hξ) (hbl ξ hξ)
      (hWre ξ hξ) (hWdich ξ hξ) hL hLV
  set F := htfin.toFinset with hF
  have hFmem : ∀ ξ, ξ ∈ F ↔ ξ ∈ t := fun ξ => Set.Finite.mem_toFinset htfin
  have hFne : F.Nonempty := by
    obtain ⟨ζ, hζt, _⟩ := Set.mem_iUnion₂.mp (htcov hξ₀)
    exact ⟨ζ, (hFmem ζ).mpr hζt⟩
  set δ := F.inf' hFne dfun with hδdef
  have hδle_dfun : ∀ ξ ∈ t, δ ≤ dfun ξ := fun ξ hξt => Finset.inf'_le dfun ((hFmem ξ).mpr hξt)
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    exact fun ξ hξF => hdpos ξ (htsub ((hFmem ξ).mp hξF))
  have hδρ' : ∀ ξ ∈ t, δ ≤ rho ξ / 2 :=
    fun ξ hξt => le_trans (hδle_dfun ξ hξt) (hdle ξ (htsub hξt))
  -- the per-chart pushes
  haveI : Nonempty C(X, X) := ⟨ContinuousMap.id X⟩
  have hgex : ∀ ξ ∈ t, ∃ g : C(X, X),
      (∀ x ∈ V, g x ∈ V) ∧
      (∀ x ∈ frontier V, g x = x ∨ g x ∈ V) ∧
      (∀ x ∈ frontier V ∩ core ξ, g x ∈ V) ∧
      (∀ x, g x ≠ x → x ∈ (ch ξ).symm '' Metric.closedBall ((ch ξ) ξ) (rho ξ / 2)
        ∧ f x < c + δ) := by
    intro ξ hξt
    have hξ := htsub hξt
    exact exists_push_of_chart hVo hfc (hsrc ξ hξ) (hpos ξ hξ) hδpos (hδρ' ξ hξt)
      (hbl ξ hξ) (hWre ξ hξ) (hWdich ξ hξ)
  choose! gfun hg1 hg2 hg4 hgid using hgex
  -- assemble the list and apply the composition lemma
  set l : List (C(X, X) × Set X) := F.toList.map (fun ξ => (gfun ξ, core ξ)) with hl
  have hlmem : ∀ p ∈ l, ∃ ξ ∈ t, p = (gfun ξ, core ξ) := by
    intro p hp
    rw [hl, List.mem_map] at hp
    obtain ⟨ξ, hξL, rfl⟩ := hp
    exact ⟨ξ, (hFmem ξ).mp (Finset.mem_toList.mp hξL), rfl⟩
  have key := exists_comp_push (L := L) hVo l
    (fun p hp x hx => by obtain ⟨ξ, hξt, rfl⟩ := hlmem p hp; exact hg1 ξ hξt x hx)
    (fun p hp x hx => by obtain ⟨ξ, hξt, rfl⟩ := hlmem p hp; exact hg2 ξ hξt x hx)
    (fun p hp x hx => by obtain ⟨ξ, hξt, rfl⟩ := hlmem p hp; exact hg4 ξ hξt x hx)
    (fun p hp x hxL => by
      obtain ⟨ξ, hξt, rfl⟩ := hlmem p hp
      by_contra hne
      obtain ⟨hxC, hlt⟩ := hgid ξ hξt x hne
      have hgap : c + dfun ξ ≤ f x := hdgap ξ (htsub hξt) x ⟨hxL, hxC⟩
      have : c + δ ≤ f x := le_trans (by linarith [hδle_dfun ξ hξt]) hgap
      linarith)
    (by
      intro x hx
      obtain ⟨ξ, hξt, hxc⟩ := Set.mem_iUnion₂.mp (htcov hx)
      rw [Set.mem_iUnion₂]
      exact ⟨(gfun ξ, core ξ),
        by rw [hl, List.mem_map]; exact ⟨ξ, Finset.mem_toList.mpr ((hFmem ξ).mpr hξt), rfl⟩, hxc⟩)
  exact ⟨compList l, key.1, key.2⟩

/-- **Open ↔ closed transfer (W7 step L5.6).**  If `V` is an open level-set
piece with a harmonic straightening collar (dichotomy `hdich`, level `hfc`,
chart germs `hchart`) whose closure is simply connected, then `V` itself is
simply connected. -/
theorem isSimplyConnected_of_closure [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ}
    (hVo : IsOpen V) (hVcl : IsCompact (closure V))
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hcl_sc : IsSimplyConnected (closure V)) :
    IsSimplyConnected V := by
  have hclpc : IsPathConnected (closure V) := hcl_sc.isPathConnected
  have hloop := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hcl_sc).2
  have hVne : V.Nonempty := by
    have := hclpc.nonempty; rwa [closure_nonempty_iff] at this
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  refine ⟨?_, ?_⟩
  · -- path-connectivity of `V`
    obtain ⟨v₀, hv₀⟩ := hVne
    rw [isPathConnected_iff]
    refine ⟨⟨v₀, hv₀⟩, fun a ha b hb => ?_⟩
    obtain ⟨qp, hqp⟩ := hclpc.joinedIn a (subset_closure ha) b (subset_closure hb)
    obtain ⟨g, hgV, hgid⟩ := exists_push_into hVo hVcl hdich hfc hchart
      (L := {a, b}) ((Set.finite_singleton b).insert a).isCompact
      (Set.insert_subset ha (Set.singleton_subset_iff.mpr hb))
    refine ⟨⟨⟨fun s => g (qp s), g.continuous.comp (map_continuous qp)⟩, ?_, ?_⟩,
      fun s => hgV (qp s) (hqp s)⟩
    · show g (qp 0) = a; rw [qp.source]; exact hgid a (by simp)
    · show g (qp 1) = b; rw [qp.target]; exact hgid b (by simp)
  · -- loop condition
    intro x p hp
    obtain ⟨H, hH⟩ := hloop x p (fun t => subset_closure (hp t))
    obtain ⟨g, hgV, hgid⟩ := exists_push_into hVo hVcl hdich hfc hchart
      (L := Set.range p) (isCompact_range (map_continuous p)) (Set.range_subset_iff.mpr hp)
    exact exists_homotopy_refl_in_of_push g hgV p (fun t => hgid (p t) ⟨t, rfl⟩) H hH

end Chart

end Uniformization
