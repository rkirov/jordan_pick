/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.CircleChain
import Rado.Surface.Germs

/-!
# Periodic parametrization of a frontier component (W7 step)

Building on the local boundary-arc structure of `CircleChain.lean`
(`exists_boundary_arc`, the component facts S2/S3) and the additive conjugate
étale space `Rado.ConjEtale` of `Rado/Surface/Germs.lean`, this file proves the
**global** structure of a connected component `C = connectedComponentIn
(frontier V) x₀` of the frontier: it is a topological circle, parametrised by a
continuous `1`-periodic map `γ : ℝ → X` with `range γ = C` and injective on a
fundamental domain `Ico 0 1`.

## Analytic route

The imaginary part of a harmonic conjugate `F` of `f` (with `Re F = f`) is the
arc-length coordinate along the frontier: near a frontier point the box chart
`ψ` has `Re ψ = f`, so `Im ψ = linv` (the `CircleChain` inverse coordinate), and
any conjugate `F` differs from `ψ` by an imaginary constant, whence
`Im F = linv + const`.  Gluing these germs is exactly the additive étale space
`Rado.ConjEtale f Y` over a connected open collar `Y ⊇ C`; the evaluation map's
imaginary part `ev q = (eval q).im` is a local homeomorphism onto `ℝ` when
restricted to the fibre over `C`, and the constant-shift deck action gives the
period.
-/

open Set Metric Topology Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Collar neighbourhood setup -/

/-- From the in-scope collar data (`f` harmonic on the open `A ⊇ frontier V`,
the dichotomy `hdich`, the level `hfc`), the connected component of `A` through a
frontier point `x₀` is an open preconnected neighbourhood `Y` of the whole
frontier component `C`, on which `f` is harmonic and **nonconstant** (it exceeds
`c` at nearby `V`-points). -/
theorem exists_collar_component [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ} {A : Set X}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hharm : SurfaceHarmonicOn f A) (hAo : IsOpen A) (hfrA : frontier V ⊆ A)
    {x₀ : X} (hx₀ : x₀ ∈ frontier V) :
    ∃ Y : Set X, IsOpen Y ∧ IsPreconnected Y ∧ x₀ ∈ Y ∧ SurfaceHarmonicOn f Y ∧
      connectedComponentIn (frontier V) x₀ ⊆ Y ∧ ∃ x₁ ∈ Y, f x₁ ≠ c := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  have hx₀A : x₀ ∈ A := hfrA hx₀
  refine ⟨connectedComponentIn A x₀, hAo.connectedComponentIn,
    isPreconnected_connectedComponentIn, mem_connectedComponentIn hx₀A,
    hharm.mono (connectedComponentIn_subset _ _),
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx₀) ((connectedComponentIn_subset _ _).trans hfrA), ?_⟩
  -- a nearby `V`-point of the connected component witnesses nonconstancy
  have hx₀cl : x₀ ∈ closure V := frontier_subset_closure hx₀
  have hS : connectedComponentIn A x₀ ∩ {x | x ∈ V ↔ c < f x} ∈ 𝓝 x₀ :=
    inter_mem (hAo.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx₀A)) (hdich x₀ hx₀)
  obtain ⟨x₁, ⟨hx₁Y, hx₁d⟩, hx₁V⟩ := mem_closure_iff_nhds.mp hx₀cl _ hS
  exact ⟨x₁, hx₁Y, (hx₁d.mp hx₁V).ne'⟩

/-! ## A straightening chart is a harmonic conjugate -/

/-- A maximal-atlas chart is holomorphic (as a map `X → ℂ`) on its source. -/
theorem holomorphicOn_chart {ψ : OpenPartialHomeomorph X ℂ} (hψ : ψ ∈ riemannAtlas X) :
    HolomorphicOn (fun x => ψ x) ψ.source := by
  intro x hx
  exact transition_analyticAt (chartAt_mem_riemannAtlas x) hψ ⟨mem_chart_source ℂ x, hx⟩

/-- A straightening chart `ψ` (with `Re ψ = f` on an open box image `W ⊆ ψ.source`)
is a harmonic conjugate of `f` there. -/
theorem isConjugate_chart {f : X → ℝ} {ψ : OpenPartialHomeomorph X ℂ} {W : Set X}
    (hψ : ψ ∈ riemannAtlas X) (hWsrc : W ⊆ ψ.source) (hre : ∀ x ∈ W, (ψ x).re = f x) :
    IsConjugate f (fun x => ψ x) W :=
  ⟨(holomorphicOn_chart hψ).mono hWsrc, hre⟩

/-- **Imaginary-part rigidity.**  Two harmonic conjugates of `f` near a common
point have imaginary parts that agree, near that point, up to an additive real
constant.  (The evaluation map's imaginary part `ev` is thus a well-defined
coordinate up to translation.) -/
theorem eventuallyEq_im_add_const {f : X → ℝ} {F G : X → ℂ} {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hF : IsConjugate f F V) (hG : IsConjugate f G W)
    {y : X} (hyV : y ∈ V) (hyW : y ∈ W) :
    ∃ t : ℝ, ∀ᶠ x in 𝓝 y, (F x).im = (G x).im + t := by
  obtain ⟨t, ht⟩ := IsConjugate.eventuallyEq_add_const hV hW hF hG hyV hyW
  refine ⟨t, ?_⟩
  filter_upwards [ht] with x hx
  rw [hx]
  simp [Complex.add_im, Complex.mul_im]

/-! ## The imaginary evaluation on the fibre over the frontier -/

section Fibre

open Rado.ConjEtale

variable [T2Space X] {f : X → ℝ} {Y : Set X}

/-- The imaginary part of the conjugate evaluation: the frontier arc coordinate. -/
noncomputable def evIm (q : ConjEtale f Y) : ℝ := (ConjEtale.eval q).im

/-! ### The tautological section of a sheet -/

/-- The tautological section of the sheet of a conjugate `F` over `W`. -/
def etaleSec {W : Set X} {F : X → ℂ} (hWo : IsOpen W) (hWY : W ⊆ Y)
    (hF : IsConjugate f F W) : ↥W → ConjEtale f Y :=
  fun z => ⟨⟨z.1, (F : Filter.Germ (𝓝 z.1) ℂ)⟩, hWY z.2, W, F, hWo, z.2, hWY, hF, rfl⟩

@[simp] theorem proj_etaleSec {W : Set X} {F : X → ℂ} (hWo : IsOpen W) (hWY : W ⊆ Y)
    (hF : IsConjugate f F W) (z : ↥W) : ConjEtale.proj (etaleSec hWo hWY hF z) = z.1 := rfl

theorem eval_etaleSec {W : Set X} {F : X → ℂ} (hWo : IsOpen W) (hWY : W ⊆ Y)
    (hF : IsConjugate f F W) (z : ↥W) : ConjEtale.eval (etaleSec hWo hWY hF z) = F z.1 := by
  simp only [ConjEtale.eval, etaleSec, Rado.germValue_coe]

theorem continuous_etaleSec {W : Set X} {F : X → ℂ} (hWo : IsOpen W) (hWY : W ⊆ Y)
    (hF : IsConjugate f F W) : Continuous (etaleSec hWo hWY hF) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro S ⟨W', G, hW'o, hW'c, hW'Y, hG, rfl⟩
  have heq : etaleSec hWo hWY hF ⁻¹' ConjEtale.sheet W' G
      = Subtype.val ⁻¹' (W' ∩ {x : X | F =ᶠ[𝓝 x] G}) := by
    ext z
    simp only [etaleSec, Set.mem_preimage, ConjEtale.sheet, Set.mem_setOf_eq, Set.mem_inter_iff]
    exact and_congr Iff.rfl Filter.Germ.coe_eq
  rw [heq]
  exact (hW'o.inter Rado.isOpen_eventuallyEq_nhds).preimage continuous_subtype_val

/-! ### The constant-shift deck action -/

/-- `germValue` commutes with germ-level postcomposition. -/
theorem germValue_map {y : X} (g : ℂ → ℂ) (γ : Filter.Germ (𝓝 y) ℂ) :
    Rado.germValue (Filter.Germ.map g γ) = g (Rado.germValue γ) := by
  induction γ using Filter.Germ.inductionOn with
  | _ F => rw [Filter.Germ.map_coe]; simp only [Rado.germValue_coe, Function.comp_apply]

/-- **Constant-shift deck action.**  Adding `r·I` to every conjugate germ is an
endomorphism of the étale space over `Y`: it commutes with `proj` and shifts
`eval` (hence `evIm`) by the constant. -/
noncomputable def shift (r : ℝ) (q : ConjEtale f Y) : ConjEtale f Y :=
  ⟨⟨q.1.1, Filter.Germ.map (fun z => z + (r : ℂ) * Complex.I) q.1.2⟩, by
    obtain ⟨hqY, V, F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
    refine ⟨hqY, V, fun z => F z + (r : ℂ) * Complex.I, hVo, hqV, hVY,
      hF.add_const_mul_I r, ?_⟩
    rw [hgerm, Filter.Germ.map_coe]; rfl⟩

@[simp] theorem proj_shift (r : ℝ) (q : ConjEtale f Y) :
    ConjEtale.proj (shift r q) = ConjEtale.proj q := rfl

theorem eval_shift (r : ℝ) (q : ConjEtale f Y) :
    ConjEtale.eval (shift r q) = ConjEtale.eval q + (r : ℂ) * Complex.I := by
  show Rado.germValue (Filter.Germ.map _ q.1.2) = _
  rw [germValue_map]; rfl

@[simp] theorem evIm_shift (r : ℝ) (q : ConjEtale f Y) : evIm (shift r q) = evIm q + r := by
  simp only [evIm, eval_shift, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]

theorem shift_shift (r s : ℝ) (q : ConjEtale f Y) : shift r (shift s q) = shift (r + s) q := by
  apply Subtype.ext
  refine Sigma.ext rfl (heq_of_eq ?_)
  show Filter.Germ.map (fun z => z + (r : ℂ) * Complex.I)
        (Filter.Germ.map (fun z => z + (s : ℂ) * Complex.I) q.1.2)
      = Filter.Germ.map (fun z => z + ((r + s : ℝ) : ℂ) * Complex.I) q.1.2
  rw [Filter.Germ.map_map]
  congr 1
  ext z
  simp only [Function.comp_apply]
  push_cast
  ring

theorem shift_zero (q : ConjEtale f Y) : shift 0 q = q := by
  apply Subtype.ext
  refine Sigma.ext rfl (heq_of_eq ?_)
  show Filter.Germ.map (fun z => z + ((0 : ℝ) : ℂ) * Complex.I) q.1.2 = q.1.2
  have hid : (fun z : ℂ => z + ((0 : ℝ) : ℂ) * Complex.I) = id := by ext z; simp
  rw [hid]
  exact congrFun Filter.Germ.map_id q.1.2

theorem shift_neg_shift (r : ℝ) (q : ConjEtale f Y) : shift (-r) (shift r q) = q := by
  rw [shift_shift, neg_add_cancel, shift_zero]

theorem shift_shift_neg (r : ℝ) (q : ConjEtale f Y) : shift r (shift (-r) q) = q := by
  rw [shift_shift, add_neg_cancel, shift_zero]

/-- Germ-level solving: `map (·+a) γ = G` iff `γ = G - a`. -/
theorem germ_map_add_eq_iff {y : X} (a : ℂ) (γ : Filter.Germ (𝓝 y) ℂ) (G : X → ℂ) :
    Filter.Germ.map (fun z => z + a) γ = (G : Filter.Germ (𝓝 y) ℂ)
      ↔ γ = ((fun z => G z - a : X → ℂ) : Filter.Germ (𝓝 y) ℂ) := by
  induction γ using Filter.Germ.inductionOn with
  | _ F =>
    rw [Filter.Germ.map_coe, Filter.Germ.coe_eq, Filter.Germ.coe_eq]
    constructor
    · intro h
      filter_upwards [h] with z hz
      simp only [Function.comp_apply] at hz
      linear_combination hz
    · intro h
      filter_upwards [h] with z hz
      simp only [Function.comp_apply]
      linear_combination hz

/-- Sheet membership transforms under the deck action by shifting the branch. -/
theorem shift_mem_sheet (r : ℝ) {W : Set X} {G : X → ℂ} (q : ConjEtale f Y) :
    shift r q ∈ ConjEtale.sheet W G
      ↔ q ∈ ConjEtale.sheet W (fun z => G z - (r : ℂ) * Complex.I) := by
  simp only [ConjEtale.sheet, Set.mem_setOf_eq]
  exact and_congr Iff.rfl (germ_map_add_eq_iff ((r : ℂ) * Complex.I) q.1.2 G)

/-- The deck action is continuous: preimages of basic sheets are basic sheets
(shifted by `-r`). -/
theorem continuous_shift (r : ℝ) : Continuous (shift (f := f) (Y := Y) r) := by
  rw [continuous_generateFrom_iff]
  rintro S ⟨W, G, hWo, hWc, hWY, hG, rfl⟩
  have hGr : IsConjugate f (fun z => G z - (r : ℂ) * Complex.I) W := by
    have h := hG.add_const_mul_I (-r)
    have heq : (fun z => G z + ((-r : ℝ) : ℂ) * Complex.I)
        = (fun z => G z - (r : ℂ) * Complex.I) := by ext z; push_cast; ring
    rwa [heq] at h
  have hpre : shift r ⁻¹' ConjEtale.sheet (u := f) (Y := Y) W G
      = ConjEtale.sheet (u := f) (Y := Y) W (fun z => G z - (r : ℂ) * Complex.I) := by
    ext q
    simp only [Set.mem_preimage]
    exact shift_mem_sheet r q
  rw [hpre]
  exact isOpen_of_mem_basicSets ⟨W, _, hWo, hWc, hWY, hGr, rfl⟩

/-- The deck action packaged as a self-homeomorphism of the étale space. -/
noncomputable def shiftHomeo (r : ℝ) : ConjEtale f Y ≃ₜ ConjEtale f Y where
  toFun := shift r
  invFun := shift (-r)
  left_inv := shift_neg_shift r
  right_inv := shift_shift_neg r
  continuous_toFun := continuous_shift r
  continuous_invFun := continuous_shift (-r)

/-- The real part of the evaluation recovers the collar coordinate. -/
theorem re_eval (q : ConjEtale f Y) : (ConjEtale.eval q).re = f (ConjEtale.proj q) := by
  obtain ⟨hqY, V', F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
  have hev : ConjEtale.eval q = F (ConjEtale.proj q) := by
    simp only [ConjEtale.eval, ConjEtale.proj, hgerm, germValue_coe]
  rw [hev]
  exact hF.2 _ hqV

/-- `evIm` is continuous. -/
theorem continuous_evIm : Continuous (evIm (f := f) (Y := Y)) :=
  Complex.continuous_im.comp continuous_eval

/-- **Local injectivity of `evIm` on the frontier fibre.**  Since the real part of
`eval` equals the collar coordinate `f`, which is the constant `c` on the frontier,
`eval` is determined by `evIm` there; local injectivity of `evIm` therefore reduces
to the discreteness of the fibres of `eval` (`Rado.ConjEtale.eval_discrete_fibers`). -/
theorem evIm_locally_injective {V : Set X} {c : ℝ}
    (hYo : IsOpen Y) (hYc : IsPreconnected Y) (hfY : SurfaceHarmonicOn f Y)
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    {x₀ x₁ : X} (hx₀Y : x₀ ∈ Y) (hx₁Y : x₁ ∈ Y) (hfne : f x₀ ≠ f x₁)
    (q : ConjEtale f Y) (hqfr : ConjEtale.proj q ∈ frontier V) :
    ∃ U ∈ 𝓝 q, ∀ w ∈ U, ConjEtale.proj w ∈ frontier V → evIm w = evIm q → w = q := by
  obtain ⟨U, hU, hUprop⟩ := eval_discrete_fibers hfY hYo hYc hx₀Y hx₁Y hfne q
  refine ⟨U, hU, fun w hwU hwfr hwev => hUprop w hwU ?_⟩
  apply Complex.ext
  · rw [re_eval, re_eval, hfc _ hwfr, hfc _ hqfr]
  · exact hwev

/-- **Injectivity engine.**  Two conjugate germs over the same base point with the
same evaluation are equal: equal value pins the imaginary constant to `0` by
rigidity.  Hence `(proj, eval)` is globally injective on the étale space, and on
the frontier fibre `(proj, evIm)` is injective (since `Re ∘ eval = f`). -/
theorem eq_of_proj_eq_eval_eq {q₁ q₂ : ConjEtale f Y}
    (hproj : ConjEtale.proj q₁ = ConjEtale.proj q₂)
    (heval : ConjEtale.eval q₁ = ConjEtale.eval q₂) : q₁ = q₂ := by
  obtain ⟨h1Y, V₁, F₁, hV₁o, hq₁V, hV₁Y, hF₁, hg₁⟩ := q₁.2
  obtain ⟨h2Y, V₂, F₂, hV₂o, hq₂V, hV₂Y, hF₂, hg₂⟩ := q₂.2
  have hq₂V' : ConjEtale.proj q₁ ∈ V₂ := by rw [hproj]; exact hq₂V
  obtain ⟨t, ht⟩ :=
    IsConjugate.eventuallyEq_add_const hV₁o hV₂o hF₁ hF₂ hq₁V hq₂V'
  have he1 : ConjEtale.eval q₁ = F₁ (ConjEtale.proj q₁) := by
    simp only [ConjEtale.eval, ConjEtale.proj, hg₁, Rado.germValue_coe]
  have he2 : ConjEtale.eval q₂ = F₂ (ConjEtale.proj q₂) := by
    simp only [ConjEtale.eval, ConjEtale.proj, hg₂, Rado.germValue_coe]
  have hval : F₁ (ConjEtale.proj q₁) = F₂ (ConjEtale.proj q₁) + (t : ℂ) * Complex.I :=
    ht.self_of_nhds
  have ht0 : t = 0 := by
    have h1 : F₁ (ConjEtale.proj q₁) = F₂ (ConjEtale.proj q₂) := by rw [← he1, ← he2, heval]
    rw [hval, ← hproj] at h1
    have h2 : (t : ℂ) * Complex.I = 0 := by linear_combination h1
    simpa only [mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero] using h2
  have hgeq : F₁ =ᶠ[𝓝 (ConjEtale.proj q₁)] F₂ := by
    filter_upwards [ht] with z hz; rw [hz, ht0]; simp
  refine ConjEtale.injOn_proj_sheet (V := Set.univ) (F := F₂) ⟨Set.mem_univ _, ?_⟩
    ⟨Set.mem_univ _, ?_⟩ hproj
  · rw [hg₁]; exact Filter.Germ.coe_eq.mpr hgeq
  · exact hg₂

/-- On the frontier fibre, `(proj, evIm)` is injective. -/
theorem eq_of_proj_eq_evIm_eq {V : Set X} {c : ℝ} (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    {q₁ q₂ : ConjEtale f Y} (h₁ : ConjEtale.proj q₁ ∈ frontier V)
    (h₂ : ConjEtale.proj q₂ ∈ frontier V)
    (hproj : ConjEtale.proj q₁ = ConjEtale.proj q₂) (hev : evIm q₁ = evIm q₂) : q₁ = q₂ := by
  refine eq_of_proj_eq_eval_eq hproj (Complex.ext ?_ hev)
  rw [re_eval, re_eval, hfc _ h₁, hfc _ h₂]

end Fibre

/-! ## Local `evIm`-charts on the fibre over a frontier component -/

section LocalChart

variable [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
  (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
  (hfc : ∀ ξ ∈ frontier V, f ξ = c)
  (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
        (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
  {Y : Set X} (hYo : IsOpen Y) {x₀ : X}

include hVo hdich hfc hchart hYo in
/-- **Local `evIm`-section (Stage 1).**  Through every étale point `q` over a
point of the frontier component `C = connectedComponentIn (frontier V) x₀` there is
a continuous local section `σ` of `evIm`: on an open interval around `evIm q`,
`evIm ∘ σ = id`, `σ (evIm q) = q`, and `σ` lands in the fibre `proj⁻¹ C`.  This
exhibits `evIm` as a local homeomorphism on `proj⁻¹ C`. -/
theorem exists_evIm_section (hCY : connectedComponentIn (frontier V) x₀ ⊆ Y)
    {q : ConjEtale f Y} (hqC : ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀) :
    ∃ (a b : ℝ) (σ : ℝ → ConjEtale f Y), a < b ∧ evIm q ∈ Set.Ioo a b ∧
      ContinuousOn σ (Set.Ioo a b) ∧ σ (evIm q) = q ∧
      (∀ s ∈ Set.Ioo a b, evIm (σ s) = s) ∧
      (∀ s ∈ Set.Ioo a b,
        ConjEtale.proj (σ s) ∈ connectedComponentIn (frontier V) x₀) := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  have hξfr : ConjEtale.proj q ∈ frontier V := connectedComponentIn_subset _ _ hqC
  set ξ := ConjEtale.proj q with hξ
  -- straightened box at ξ
  obtain ⟨ψ, δ, ε, hψ, hξψ, hδ, hε, hqre, hbox_tgt, hWopen, hξW, hf_eq, hVcap, hfront⟩ :=
    exists_straight_box hVo hdich hfc hchart hξfr
  set box := straightBox (ψ ξ) c δ ε with hbox
  set W := ψ.symm '' box with hWdef
  set m := (ψ ξ).im with hm
  set seg : ℝ → ℂ := fun s => (c : ℂ) + (s : ℂ) * Complex.I with hseg
  have hseg_re : ∀ s, (seg s).re = c := by intro s; simp [hseg]
  have hseg_im : ∀ s, (seg s).im = s := by intro s; simp [hseg]
  set arc : ℝ → X := fun s => ψ.symm (seg s) with harc
  set a := m - ε with ha
  set b := m + ε with hb
  have hab : a < b := by rw [ha, hb]; linarith
  -- box membership of segment points
  have hseg_box : ∀ s ∈ Set.Ioo a b, seg s ∈ box := by
    intro s hs
    rw [hbox, mem_straightBox, hseg_re, hseg_im]
    refine ⟨by rw [sub_self, abs_zero]; exact hδ, ?_⟩
    rw [abs_lt]; constructor <;> [linarith [hs.1]; linarith [hs.2]]
  have hseg_mid : ∀ s ∈ Set.Ioo a b, seg s ∈ {z ∈ box | z.re = c} :=
    fun s hs => ⟨hseg_box s hs, hseg_re s⟩
  have harc_mem : ∀ s ∈ Set.Ioo a b, arc s ∈ frontier V ∩ W := by
    intro s hs; rw [hfront]; exact ⟨seg s, hseg_mid s hs, rfl⟩
  have hψarc : ∀ s ∈ Set.Ioo a b, ψ (arc s) = seg s := by
    intro s hs; exact ψ.right_inv (hbox_tgt (hseg_box s hs))
  -- `W ⊆ ψ.source`
  have hWsrc : W ⊆ ψ.source := by rintro x ⟨z, hz, rfl⟩; exact ψ.map_target (hbox_tgt hz)
  -- `frontier V ∩ W = arc '' Ioo a b`, hence preconnected, hence ⊆ C
  have himg : frontier V ∩ W = arc '' Set.Ioo a b := by
    apply Set.Subset.antisymm
    · rw [hfront]
      rintro _ ⟨z, ⟨hzbox, hzre⟩, rfl⟩
      have hzim : z.im ∈ Set.Ioo a b := by
        rw [hbox, mem_straightBox] at hzbox
        have := hzbox.2; rw [abs_lt] at this
        exact ⟨by rw [ha]; linarith [this.1], by rw [hb]; linarith [this.2]⟩
      refine ⟨z.im, hzim, ?_⟩
      show ψ.symm (seg z.im) = ψ.symm z
      congr 1
      apply Complex.ext
      · rw [hseg_re, hzre]
      · rw [hseg_im]
    · rintro _ ⟨s, hs, rfl⟩; exact harc_mem s hs
  have hcont_arc : ContinuousOn arc (Set.Ioo a b) := by
    have hsegc : Continuous seg := by rw [hseg]; fun_prop
    exact ψ.continuousOn_symm.comp hsegc.continuousOn
      (fun s hs => hbox_tgt (hseg_box s hs))
  have hpre : IsPreconnected (frontier V ∩ W) := by
    rw [himg]; exact isPreconnected_Ioo.image arc hcont_arc
  have hsubC : frontier V ∩ W ⊆ C := by
    have h1 : frontier V ∩ W ⊆ connectedComponentIn (frontier V) ξ :=
      hpre.subset_connectedComponentIn ⟨hξfr, hξW⟩ Set.inter_subset_left
    rwa [hC, connectedComponentIn_eq hqC]
  -- `ψ` is a conjugate of `f` on `W ∩ Y`
  have hWYo : IsOpen (W ∩ Y) := hWopen.inter hYo
  have hψconj : IsConjugate f (fun x => ψ x) (W ∩ Y) :=
    (isConjugate_chart hψ hWsrc
      (fun x hx => re_eq_f_of_mem_boxImage hbox_tgt hf_eq hx)).mono Set.inter_subset_left
  -- membership of `arc s` in `W ∩ Y` for `s ∈ Ioo a b`
  have harc_WY : ∀ s ∈ Set.Ioo a b, arc s ∈ W ∩ Y := by
    intro s hs
    exact ⟨(harc_mem s hs).2, hCY (hsubC (harc_mem s hs))⟩
  -- q's branch and the rigidity constant
  obtain ⟨hqY, VF, F, hVFo, hqVF, hVFY, hF, hgerm⟩ := q.2
  have hψconjV : IsConjugate f (fun x => ψ x) W :=
    isConjugate_chart hψ hWsrc (fun x hx => re_eq_f_of_mem_boxImage hbox_tgt hf_eq hx)
  obtain ⟨t', ht'⟩ :=
    IsConjugate.eventuallyEq_add_const hVFo hWopen hF hψconjV hqVF hξW
  -- `t' = evIm q - m`
  have hevq : evIm q = m + t' := by
    have hFξ : F ξ = ψ ξ + (t' : ℂ) * Complex.I := ht'.self_of_nhds
    have : evIm q = (F ξ).im := by
      show (ConjEtale.eval q).im = _
      have : ConjEtale.eval q = F ξ := by
        simp only [ConjEtale.eval, hgerm, Rado.germValue_coe]; rfl
      rw [this]
    rw [this, hFξ]
    simp [Complex.add_im, Complex.mul_im, hm]
  set t := t' with ht
  -- the ψ-point over `arc s` (partial section), and the shifted section
  set P : ℝ → ConjEtale f Y := fun s =>
    if h : arc (s - t) ∈ W ∩ Y then
      etaleSec hWYo Set.inter_subset_right hψconj ⟨arc (s - t), h⟩
    else q with hP
  set σ : ℝ → ConjEtale f Y := fun s => shift t (P s) with hσ
  set a' := a + t with ha'
  set b' := b + t with hb'
  have hab' : a' < b' := by rw [ha', hb']; linarith
  -- subtype-safe bounds transfer
  have hshiftmem : ∀ s ∈ Set.Ioo a' b', s - t ∈ Set.Ioo a b := by
    intro s hs
    exact ⟨by have := hs.1; rw [ha'] at this; linarith,
           by have := hs.2; rw [hb'] at this; linarith⟩
  have hshift : ∀ s ∈ Set.Ioo a' b', arc (s - t) ∈ W ∩ Y :=
    fun s hs => harc_WY _ (hshiftmem s hs)
  -- unfold `P` on the interval
  have hPeq : ∀ s (h : arc (s - t) ∈ W ∩ Y),
      P s = etaleSec hWYo Set.inter_subset_right hψconj ⟨arc (s - t), h⟩ := by
    intro s h; simp only [hP]; rw [dif_pos h]
  -- evIm of the section
  have hevσ : ∀ s ∈ Set.Ioo a' b', evIm (σ s) = s := by
    intro s hs
    have hin : s - t ∈ Set.Ioo a b := hshiftmem s hs
    show evIm (shift t (P s)) = s
    rw [evIm_shift, hPeq s (hshift s hs)]
    have : evIm (etaleSec hWYo Set.inter_subset_right hψconj ⟨arc (s - t), hshift s hs⟩)
        = s - t := by
      show (ConjEtale.eval _).im = s - t
      rw [eval_etaleSec]
      show (ψ (arc (s - t))).im = s - t
      rw [hψarc (s - t) hin, hseg_im]
    rw [this]; ring
  -- projection of the section lands in the frontier component
  have hprojσ : ∀ s ∈ Set.Ioo a' b', ConjEtale.proj (σ s) ∈ C := by
    intro s hs
    have hin : s - t ∈ Set.Ioo a b := hshiftmem s hs
    show ConjEtale.proj (shift t (P s)) ∈ C
    rw [proj_shift, hPeq s (hshift s hs), proj_etaleSec]
    exact hsubC (harc_mem (s - t) hin)
  -- continuity of the section
  have hcontσ : ContinuousOn σ (Set.Ioo a' b') := by
    rw [continuousOn_iff_continuous_restrict]
    have hcont1 : Continuous (fun z : ↥(Set.Ioo a' b') =>
        (⟨arc (z.1 - t), hshift z.1 z.2⟩ : ↥(W ∩ Y))) := by
      apply Continuous.subtype_mk
      have hsub : Continuous (fun z : ↥(Set.Ioo a' b') => z.1 - t) :=
        continuous_subtype_val.sub continuous_const
      exact hcont_arc.comp_continuous hsub (fun z => hshiftmem z.1 z.2)
    have hEq : Set.restrict (Set.Ioo a' b') σ
        = fun z => shift t (etaleSec hWYo Set.inter_subset_right hψconj
            ⟨arc (z.1 - t), hshift z.1 z.2⟩) := by
      funext z
      show shift t (P z.1) = _
      rw [hPeq z.1 (hshift z.1 z.2)]
    rw [hEq]
    exact (continuous_shift t).comp ((continuous_etaleSec hWYo _ hψconj).comp hcont1)
  -- the section passes through `q`
  have hσq : σ (evIm q) = q := by
    have hin : evIm q - t ∈ Set.Ioo a b := by
      have he : evIm q - t = m := by rw [hevq]; ring
      rw [he]; exact ⟨by rw [ha]; linarith, by rw [hb]; linarith⟩
    have hmem : arc (evIm q - t) ∈ W ∩ Y := harc_WY _ hin
    have harceq : arc (evIm q - t) = ξ := by
      have he : evIm q - t = m := by rw [hevq]; ring
      rw [he]
      show ψ.symm (seg m) = ξ
      have hsm : seg m = ψ ξ := by
        apply Complex.ext
        · rw [hseg_re]; exact hqre.symm
        · rw [hseg_im, hm]
      rw [hsm, ψ.left_inv hξψ]
    show shift t (P (evIm q)) = q
    rw [hPeq (evIm q) hmem]
    refine ConjEtale.injOn_proj_sheet (V := Set.univ)
      (F := fun x => ψ x + (t : ℂ) * Complex.I) ?_ ?_ harceq
    · refine ⟨Set.mem_univ _, ?_⟩
      show Filter.Germ.map (fun z => z + (t : ℂ) * Complex.I)
          ((fun x => ψ x : Filter.Germ (𝓝 (arc (evIm q - t))) ℂ))
        = ((fun x => ψ x + (t : ℂ) * Complex.I : X → ℂ) :
            Filter.Germ (𝓝 (arc (evIm q - t))) ℂ)
      rw [Filter.Germ.map_coe]; rfl
    · refine ⟨Set.mem_univ _, ?_⟩
      rw [hgerm]
      exact Filter.Germ.coe_eq.mpr ht'
  refine ⟨a', b', σ, hab', ?_, hcontσ, hσq, hevσ, hprojσ⟩
  rw [hevq]
  exact ⟨by rw [ha', ha]; linarith, by rw [hb', hb]; linarith⟩

end LocalChart

/-! ## Stage 2 — the fibre component `Ê` and `evIm : Ê → ℝ` -/

section Monodromy

variable [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
  (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
  (hfc : ∀ ξ ∈ frontier V, f ξ = c)
  (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
        (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
  {Y : Set X} (hYo : IsOpen Y) {x₀ : X}
  (hCY : connectedComponentIn (frontier V) x₀ ⊆ Y)

/-- Abbreviation for the frontier fibre `P = proj⁻¹ C`. -/
local notation3 "P" => ConjEtale.proj (u := f) (Y := Y) ⁻¹'
  connectedComponentIn (frontier V) x₀

include hVo hdich hfc hchart hYo hCY in
/-- **Sections stay in the component.**  The `evIm`-section through a point `q` of
the fibre `P` (from `exists_evIm_section`) has its whole image inside the connected
component `connectedComponentIn P q`.  (Its image is a connected subset of `P`
containing `q`.) -/
theorem section_subset_component {q : ConjEtale f Y}
    (hqC : ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀) :
    ∃ (a b : ℝ) (σ : ℝ → ConjEtale f Y), a < b ∧ evIm q ∈ Set.Ioo a b ∧
      ContinuousOn σ (Set.Ioo a b) ∧ σ (evIm q) = q ∧
      (∀ s ∈ Set.Ioo a b, evIm (σ s) = s) ∧
      σ '' Set.Ioo a b ⊆ connectedComponentIn
        (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q := by
  obtain ⟨a, b, σ, hab, hmem, hcont, hσq, hev, hproj⟩ :=
    exists_evIm_section hVo hdich hfc hchart hYo hCY hqC
  refine ⟨a, b, σ, hab, hmem, hcont, hσq, hev, ?_⟩
  have hpre : IsPreconnected (σ '' Set.Ioo a b) := isPreconnected_Ioo.image σ hcont
  have hqin : q ∈ σ '' Set.Ioo a b := ⟨evIm q, hmem, hσq⟩
  have hsubP : σ '' Set.Ioo a b ⊆
      ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀ := by
    rintro _ ⟨s, hs, rfl⟩; exact hproj s hs
  exact hpre.subset_connectedComponentIn hqin hsubP

include hVo hdich hfc hchart hYo hCY in
/-- **`evIm` maps the fibre component to an open set.**  Through each point of
`Ê = connectedComponentIn P q₀` there is a local section whose image lies in `Ê`
and whose `evIm`-image is an open interval; hence `evIm '' Ê` is open. -/
theorem isOpen_evIm_image_component (q₀ : ConjEtale f Y) :
    IsOpen (evIm '' connectedComponentIn
      (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀) := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨q, hqE, rfl⟩
  have hqP : q ∈ ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀ :=
    connectedComponentIn_subset _ _ hqE
  have hqC : ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀ := hqP
  obtain ⟨a, b, σ, hab, hmem, _, hσq, hev, hsub⟩ :=
    section_subset_component hVo hdich hfc hchart hYo hCY hqC
  -- the section image lies in `Ê`
  have hEq : connectedComponentIn
      (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q
      = connectedComponentIn
        (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀ :=
    (connectedComponentIn_eq hqE).symm
  rw [hEq] at hsub
  -- `Ioo a b ⊆ evIm '' Ê`
  have hIoo : Set.Ioo a b ⊆ evIm '' connectedComponentIn
      (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀ := by
    intro s hs
    exact ⟨σ s, hsub ⟨s, hs, rfl⟩, hev s hs⟩
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hmem) hIoo

/-- `evIm '' Ê` is preconnected: `Ê` is preconnected and `evIm` is continuous. -/
theorem isPreconnected_evIm_image_component (q₀ : ConjEtale f Y) :
    IsPreconnected (evIm '' connectedComponentIn
      (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀) :=
  isPreconnected_connectedComponentIn.image _ continuous_evIm.continuousOn

end Monodromy

/-! ## Stage 2 endgame — sheet openness and the local homeomorphism structure -/

section SheetOpen

open Rado.ConjEtale

variable {f : X → ℝ} {Y : Set X}

/-- **Sheets are open.**  A sheet `sheet V F` of a conjugate `F` over an open
`V ⊆ Y` is open: every point projects into `V`, and (local connectedness) sits in
a preconnected open sub-box, which is a basic open set. -/
theorem isOpen_sheet {V : Set X} {F : X → ℂ} (hVo : IsOpen V) (hVY : V ⊆ Y)
    (hF : IsConjugate f F V) : IsOpen (ConjEtale.sheet (u := f) (Y := Y) V F) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hqV : ConjEtale.proj q ∈ V := hq.1
  set V' := connectedComponentIn V (ConjEtale.proj q) with hV'
  have hV'o : IsOpen V' := hVo.connectedComponentIn
  have hV'p : IsPreconnected V' := isPreconnected_connectedComponentIn
  have hqV' : ConjEtale.proj q ∈ V' := mem_connectedComponentIn hqV
  have hV'V : V' ⊆ V := connectedComponentIn_subset _ _
  have hF' : IsConjugate f F V' := hF.mono hV'V
  have hopen : IsOpen (ConjEtale.sheet (u := f) (Y := Y) V' F) :=
    ConjEtale.isOpen_of_mem_basicSets ⟨V', F, hV'o, hV'p, hV'V.trans hVY, hF', rfl⟩
  have hqmem : q ∈ ConjEtale.sheet (u := f) (Y := Y) V' F := ⟨hqV', hq.2⟩
  refine Filter.mem_of_superset (hopen.mem_nhds hqmem) ?_
  rintro q' ⟨hq'V', hq'F⟩
  exact ⟨hV'V hq'V', hq'F⟩

/-- On a sheet, the evaluation is the value of the branch conjugate. -/
theorem eval_of_mem_sheet {V : Set X} {F : X → ℂ} {q : ConjEtale f Y}
    (hq : q ∈ ConjEtale.sheet V F) : ConjEtale.eval q = F (ConjEtale.proj q) := by
  simp only [ConjEtale.eval, ConjEtale.proj, hq.2, Rado.germValue_coe]

end SheetOpen

/-! ## Checkpoint A — local injectivity of `evIm` on the frontier fibre and
section uniqueness -/

section LocalInj

variable [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
  (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
  (hfc : ∀ ξ ∈ frontier V, f ξ = c)
  (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
        (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
  {Y : Set X} (hYo : IsOpen Y) {x₀ : X}
  (hCY : connectedComponentIn (frontier V) x₀ ⊆ Y)

open Rado.ConjEtale

local notation3 "P" => ConjEtale.proj (u := f) (Y := Y) ⁻¹'
  connectedComponentIn (frontier V) x₀

include hVo hdich hfc hchart hYo hCY in
/-- **Local injectivity of `evIm` on the frontier fibre (Checkpoint A1').**
Through every fibre point `q` over the frontier component `C`, there is an open
neighbourhood `U` (a single sheet of a straightening chart) on which `evIm` is
injective over `P = proj⁻¹ C`.  On the frontier arc the imaginary part of the
straightening chart is a coordinate, so the branch conjugate's imaginary part is
injective there; `proj` is injective on the sheet, so `evIm` is too. -/
theorem exists_evIm_local_inj {q : ConjEtale f Y}
    (hqC : ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀) :
    ∃ U, IsOpen U ∧ q ∈ U ∧ Set.InjOn evIm (U ∩ P) := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  have hξfr : ConjEtale.proj q ∈ frontier V := connectedComponentIn_subset _ _ hqC
  set ξ := ConjEtale.proj q with hξ
  have hξY : ξ ∈ Y := hCY hqC
  -- straightened box at ξ
  obtain ⟨ψ, δ, ε, hψ, hξψ, hδ, hε, hqre, hbox_tgt, hWopen, hξW, hf_eq, _hVcap, hfront⟩ :=
    exists_straight_box hVo hdich hfc hchart hξfr
  set box := straightBox (ψ ξ) c δ ε with hbox
  set W := ψ.symm '' box with hWdef
  -- `W ⊆ ψ.source`
  have hWsrc : W ⊆ ψ.source := by rintro x ⟨z, hz, rfl⟩; exact ψ.map_target (hbox_tgt hz)
  -- `ψ` is a conjugate of `f` on `W`
  have hψconjW : IsConjugate f (fun x => ψ x) W :=
    isConjugate_chart hψ hWsrc (fun x hx => re_eq_f_of_mem_boxImage hbox_tgt hf_eq hx)
  -- injectivity of the chart's imaginary part on the frontier slice
  have hinj_im : ∀ x₁ ∈ frontier V ∩ W, ∀ x₂ ∈ frontier V ∩ W,
      (ψ x₁).im = (ψ x₂).im → x₁ = x₂ := by
    intro x₁ hx₁ x₂ hx₂ him
    rw [hfront] at hx₁ hx₂
    obtain ⟨z₁, ⟨hz₁box, hz₁re⟩, rfl⟩ := hx₁
    obtain ⟨z₂, ⟨hz₂box, hz₂re⟩, rfl⟩ := hx₂
    have h1 : (ψ (ψ.symm z₁)).im = z₁.im := by rw [ψ.right_inv (hbox_tgt hz₁box)]
    have h2 : (ψ (ψ.symm z₂)).im = z₂.im := by rw [ψ.right_inv (hbox_tgt hz₂box)]
    rw [h1, h2] at him
    congr 1
    exact Complex.ext (by rw [hz₁re, hz₂re]) him
  -- q's branch and the rigidity constant `t'`
  obtain ⟨hqY, VF, F, hVFo, hqVF, hVFY, hF, hgerm⟩ := q.2
  obtain ⟨t', ht'⟩ :=
    IsConjugate.eventuallyEq_add_const hVFo hWopen hF hψconjW hqVF hξW
  set G : X → ℂ := fun x => ψ x + (t' : ℂ) * Complex.I with hG
  have hGconjWY : IsConjugate f G (W ∩ Y) := (hψconjW.add_const_mul_I t').mono Set.inter_subset_left
  have hWYo : IsOpen (W ∩ Y) := hWopen.inter hYo
  -- the open sheet through `q`
  set U := ConjEtale.sheet (u := f) (Y := Y) (W ∩ Y) G with hU
  have hUopen : IsOpen U := isOpen_sheet hWYo Set.inter_subset_right hGconjWY
  have hqU : q ∈ U := by
    refine ⟨⟨hξW, hξY⟩, ?_⟩
    rw [hgerm]
    exact Filter.Germ.coe_eq.mpr ht'
  refine ⟨U, hUopen, hqU, ?_⟩
  -- `evIm` on the sheet is `(ψ ∘ proj).im + t'`
  have hevIm : ∀ w ∈ U, evIm w = (ψ (ConjEtale.proj w)).im + t' := by
    intro w hw
    have he : ConjEtale.eval w = G (ConjEtale.proj w) := eval_of_mem_sheet hw
    show (ConjEtale.eval w).im = _
    rw [he, hG]
    simp [Complex.add_im, Complex.mul_im]
  intro w₁ hw₁ w₂ hw₂ hev
  obtain ⟨hw₁U, hw₁P⟩ := hw₁
  obtain ⟨hw₂U, hw₂P⟩ := hw₂
  -- both project into the frontier slice
  have hp₁ : ConjEtale.proj w₁ ∈ frontier V ∩ W :=
    ⟨connectedComponentIn_subset _ _ hw₁P, hw₁U.1.1⟩
  have hp₂ : ConjEtale.proj w₂ ∈ frontier V ∩ W :=
    ⟨connectedComponentIn_subset _ _ hw₂P, hw₂U.1.1⟩
  have him : (ψ (ConjEtale.proj w₁)).im = (ψ (ConjEtale.proj w₂)).im := by
    have := hev
    rw [hevIm w₁ hw₁U, hevIm w₂ hw₂U] at this
    linarith
  have hproj : ConjEtale.proj w₁ = ConjEtale.proj w₂ := hinj_im _ hp₁ _ hp₂ him
  exact ConjEtale.injOn_proj_sheet hw₁U hw₂U hproj

include hVo hdich hfc hchart hYo hCY in
/-- **Section uniqueness (Checkpoint A2).**  Two continuous lifts `s₁, s₂` of the
identity along `evIm` (with values projecting into `C`) over a preconnected
parameter set `J`, agreeing at one point, agree throughout `J`.  The agreement
set is closed (Hausdorffness) and open (local injectivity of `evIm` on `P`),
hence clopen in preconnected `J`. -/
theorem section_unique {J : Set ℝ} (hJ : IsPreconnected J)
    {s₁ s₂ : ℝ → ConjEtale f Y}
    (hc₁ : ContinuousOn s₁ J) (hc₂ : ContinuousOn s₂ J)
    (hev₁ : ∀ t ∈ J, evIm (s₁ t) = t) (hev₂ : ∀ t ∈ J, evIm (s₂ t) = t)
    (hP₁ : ∀ t ∈ J, ConjEtale.proj (s₁ t) ∈ connectedComponentIn (frontier V) x₀)
    (hP₂ : ∀ t ∈ J, ConjEtale.proj (s₂ t) ∈ connectedComponentIn (frontier V) x₀)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hagree : s₁ t₀ = s₂ t₀) :
    ∀ t ∈ J, s₁ t = s₂ t := by
  classical
  haveI : T2Space (ConjEtale f Y) := ConjEtale.t2Space
  haveI : PreconnectedSpace ↥J := Subtype.preconnectedSpace hJ
  have hcont₁ : Continuous (J.restrict s₁) := continuousOn_iff_continuous_restrict.mp hc₁
  have hcont₂ : Continuous (J.restrict s₂) := continuousOn_iff_continuous_restrict.mp hc₂
  set E : Set ↥J := {t | J.restrict s₁ t = J.restrict s₂ t} with hE
  have hEclosed : IsClosed E := isClosed_eq hcont₁ hcont₂
  have hEopen : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro t₀' ht₀'E
    have hqC : ConjEtale.proj (s₁ t₀'.1) ∈ connectedComponentIn (frontier V) x₀ :=
      hP₁ t₀'.1 t₀'.2
    obtain ⟨U, hUo, hqU, hUinj⟩ :=
      exists_evIm_local_inj hVo hdich hfc hchart hYo hCY hqC
    have heq₀ : s₁ t₀'.1 = s₂ t₀'.1 := ht₀'E
    have hqU₂ : s₂ t₀'.1 ∈ U := heq₀ ▸ hqU
    have hpre₁ : J.restrict s₁ ⁻¹' U ∈ 𝓝 t₀' :=
      hcont₁.continuousAt.preimage_mem_nhds (hUo.mem_nhds hqU)
    have hpre₂ : J.restrict s₂ ⁻¹' U ∈ 𝓝 t₀' :=
      hcont₂.continuousAt.preimage_mem_nhds (hUo.mem_nhds hqU₂)
    refine Filter.mem_of_superset (Filter.inter_mem hpre₁ hpre₂) ?_
    intro t ht
    have h1P : s₁ t.1 ∈ U ∩ (ConjEtale.proj (u := f) (Y := Y) ⁻¹'
        connectedComponentIn (frontier V) x₀) := ⟨ht.1, hP₁ t.1 t.2⟩
    have h2P : s₂ t.1 ∈ U ∩ (ConjEtale.proj (u := f) (Y := Y) ⁻¹'
        connectedComponentIn (frontier V) x₀) := ⟨ht.2, hP₂ t.1 t.2⟩
    have hevs : evIm (s₁ t.1) = evIm (s₂ t.1) := by rw [hev₁ t.1 t.2, hev₂ t.1 t.2]
    exact hUinj h1P h2P hevs
  have hEuniv : E = Set.univ :=
    (IsClopen.eq_univ ⟨hEclosed, hEopen⟩ ⟨⟨t₀, ht₀⟩, hagree⟩)
  intro t ht
  have : (⟨t, ht⟩ : ↥J) ∈ E := hEuniv ▸ Set.mem_univ _
  exact this

set_option maxHeartbeats 1600000 in
include hVo hdich hfc hchart hYo hCY in
/-- **Uniform local margin (Checkpoint B core).**  At a frontier-component point
`ξ'` there is an open box `O ∋ ξ'` and a fixed margin `r > 0` such that every
fibre point `q` over a point of `O ∩ C` continues (via the box's straightening
section) `r` beyond `evIm q` on both sides, staying inside the fibre component of
`q`.  Because the box is fixed at `ξ'`, the margin `r` is uniform over `O`
(shrinking to the middle half of the box). -/
theorem margin_at {ξ' : X}
    (hξ'C : ξ' ∈ connectedComponentIn (frontier V) x₀) :
    ∃ (O : Set X) (r : ℝ), IsOpen O ∧ ξ' ∈ O ∧ 0 < r ∧
      ∀ q : ConjEtale f Y, ConjEtale.proj q ∈ O →
        ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀ →
        Set.Ioo (evIm q - r) (evIm q + r) ⊆
          evIm '' connectedComponentIn
            (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  have hξ'fr : ξ' ∈ frontier V := connectedComponentIn_subset _ _ hξ'C
  obtain ⟨ψ, δ, ε, hψ, hξ'ψ, hδ, hε, hqre, hbox_tgt, hWopen, hξ'W, hf_eq, _hVcap, hfront⟩ :=
    exists_straight_box hVo hdich hfc hchart hξ'fr
  set box := straightBox (ψ ξ') c δ ε with hbox
  set W := ψ.symm '' box with hWdef
  set m := (ψ ξ').im with hm
  set seg : ℝ → ℂ := fun s => (c : ℂ) + (s : ℂ) * Complex.I with hseg
  have hseg_re : ∀ s, (seg s).re = c := by intro s; simp [hseg]
  have hseg_im : ∀ s, (seg s).im = s := by intro s; simp [hseg]
  set arc : ℝ → X := fun s => ψ.symm (seg s) with harc
  set a := m - ε with ha
  set b := m + ε with hb
  have hab : a < b := by rw [ha, hb]; linarith
  have hseg_box : ∀ s ∈ Set.Ioo a b, seg s ∈ box := by
    intro s hs
    rw [hbox, mem_straightBox, hseg_re, hseg_im]
    refine ⟨by rw [sub_self, abs_zero]; exact hδ, ?_⟩
    rw [abs_lt]; constructor <;> [linarith [hs.1]; linarith [hs.2]]
  have hseg_mid : ∀ s ∈ Set.Ioo a b, seg s ∈ {z ∈ box | z.re = c} :=
    fun s hs => ⟨hseg_box s hs, hseg_re s⟩
  have harc_mem : ∀ s ∈ Set.Ioo a b, arc s ∈ frontier V ∩ W := by
    intro s hs; rw [hfront]; exact ⟨seg s, hseg_mid s hs, rfl⟩
  have hψarc : ∀ s ∈ Set.Ioo a b, ψ (arc s) = seg s := by
    intro s hs; exact ψ.right_inv (hbox_tgt (hseg_box s hs))
  have hWsrc : W ⊆ ψ.source := by rintro x ⟨z, hz, rfl⟩; exact ψ.map_target (hbox_tgt hz)
  have himg : frontier V ∩ W = arc '' Set.Ioo a b := by
    apply Set.Subset.antisymm
    · rw [hfront]
      rintro _ ⟨z, ⟨hzbox, hzre⟩, rfl⟩
      have hzim : z.im ∈ Set.Ioo a b := by
        rw [hbox, mem_straightBox] at hzbox
        have := hzbox.2; rw [abs_lt] at this
        exact ⟨by rw [ha]; linarith [this.1], by rw [hb]; linarith [this.2]⟩
      refine ⟨z.im, hzim, ?_⟩
      show ψ.symm (seg z.im) = ψ.symm z
      congr 1
      apply Complex.ext
      · rw [hseg_re, hzre]
      · rw [hseg_im]
    · rintro _ ⟨s, hs, rfl⟩; exact harc_mem s hs
  have hcont_arc : ContinuousOn arc (Set.Ioo a b) := by
    have hsegc : Continuous seg := by rw [hseg]; fun_prop
    exact ψ.continuousOn_symm.comp hsegc.continuousOn
      (fun s hs => hbox_tgt (hseg_box s hs))
  have hpre : IsPreconnected (frontier V ∩ W) := by
    rw [himg]; exact isPreconnected_Ioo.image arc hcont_arc
  have hsubC : frontier V ∩ W ⊆ C := by
    have h1 : frontier V ∩ W ⊆ connectedComponentIn (frontier V) ξ' :=
      hpre.subset_connectedComponentIn ⟨hξ'fr, hξ'W⟩ Set.inter_subset_left
    rwa [hC, connectedComponentIn_eq hξ'C]
  have hWYo : IsOpen (W ∩ Y) := hWopen.inter hYo
  have hψconj : IsConjugate f (fun x => ψ x) (W ∩ Y) :=
    (isConjugate_chart hψ hWsrc
      (fun x hx => re_eq_f_of_mem_boxImage hbox_tgt hf_eq hx)).mono Set.inter_subset_left
  have hψconjV : IsConjugate f (fun x => ψ x) W :=
    isConjugate_chart hψ hWsrc (fun x hx => re_eq_f_of_mem_boxImage hbox_tgt hf_eq hx)
  have harc_WY : ∀ s ∈ Set.Ioo a b, arc s ∈ W ∩ Y := by
    intro s hs
    exact ⟨(harc_mem s hs).2, hCY (hsubC (harc_mem s hs))⟩
  -- the smaller box (imaginary half-width `ε/2`) gives the open slice `O`
  have hsmall_box : straightBox (ψ ξ') c δ (ε / 2) ⊆ box := by
    intro z hz
    rw [mem_straightBox] at hz
    rw [hbox, mem_straightBox]
    exact ⟨hz.1, lt_of_lt_of_le hz.2 (by linarith)⟩
  have hsmall_tgt : straightBox (ψ ξ') c δ (ε / 2) ⊆ ψ.target := hsmall_box.trans hbox_tgt
  set W' := ψ.symm '' straightBox (ψ ξ') c δ (ε / 2) with hW'
  have hW'open : IsOpen W' :=
    ψ.symm.isOpen_image_of_subset_source (isOpen_straightBox _ _ _ _)
      (by rw [OpenPartialHomeomorph.symm_source]; exact hsmall_tgt)
  have hξ'W' : ξ' ∈ W' := by
    refine ⟨ψ ξ', ?_, ψ.left_inv hξ'ψ⟩
    rw [mem_straightBox]
    exact ⟨by rw [hqre, sub_self, abs_zero]; exact hδ,
           by rw [sub_self, abs_zero]; exact half_pos hε⟩
  refine ⟨W', ε / 2, hW'open, hξ'W', half_pos hε, ?_⟩
  intro q hqW' hqC
  set y := ConjEtale.proj q with hy
  have hyfr : y ∈ frontier V := connectedComponentIn_subset _ _ hqC
  obtain ⟨z, hz_small, hyz⟩ := hqW'
  have hz_small' := mem_straightBox.mp hz_small
  have hz_box : z ∈ box := hsmall_box hz_small
  have hyW : y ∈ W := ⟨z, hz_box, hyz⟩
  have hψy : ψ y = z := by rw [← hyz]; exact ψ.right_inv (hbox_tgt hz_box)
  have hfy : f y = z.re := by have := hf_eq z hz_box; rwa [hyz] at this
  have hzre : z.re = c := hfy.symm.trans (hfc y hyfr)
  have hzim_bd : |z.im - m| < ε / 2 := hz_small'.2
  -- q's branch and the rigidity constant `t`
  obtain ⟨hqY, VF, F, hVFo, hqVF, hVFY, hF, hgerm⟩ := q.2
  obtain ⟨t, ht'⟩ :=
    IsConjugate.eventuallyEq_add_const hVFo hWopen hF hψconjV hqVF hyW
  have heval : ConjEtale.eval q = F y := by
    simp only [ConjEtale.eval, hgerm, Rado.germValue_coe]; rfl
  have hFy : F y = ψ y + (t : ℂ) * Complex.I := ht'.self_of_nhds
  have hevq : evIm q = z.im + t := by
    show (ConjEtale.eval q).im = z.im + t
    rw [heval, hFy, hψy]
    simp [Complex.add_im, Complex.mul_im]
  -- the shifted section
  set Pf : ℝ → ConjEtale f Y := fun s =>
    if h : arc (s - t) ∈ W ∩ Y then
      etaleSec hWYo Set.inter_subset_right hψconj ⟨arc (s - t), h⟩
    else q with hPf
  set σ : ℝ → ConjEtale f Y := fun s => shift t (Pf s) with hσ
  set a' := a + t with ha'
  set b' := b + t with hb'
  have hshiftmem : ∀ s ∈ Set.Ioo a' b', s - t ∈ Set.Ioo a b := by
    intro s hs
    exact ⟨by have := hs.1; rw [ha'] at this; linarith,
           by have := hs.2; rw [hb'] at this; linarith⟩
  have hshift : ∀ s ∈ Set.Ioo a' b', arc (s - t) ∈ W ∩ Y :=
    fun s hs => harc_WY _ (hshiftmem s hs)
  have hPeq : ∀ s (h : arc (s - t) ∈ W ∩ Y),
      Pf s = etaleSec hWYo Set.inter_subset_right hψconj ⟨arc (s - t), h⟩ := by
    intro s h; simp only [hPf]; rw [dif_pos h]
  have hevσ : ∀ s ∈ Set.Ioo a' b', evIm (σ s) = s := by
    intro s hs
    have hin : s - t ∈ Set.Ioo a b := hshiftmem s hs
    show evIm (shift t (Pf s)) = s
    rw [evIm_shift, hPeq s (hshift s hs)]
    have : evIm (etaleSec hWYo Set.inter_subset_right hψconj ⟨arc (s - t), hshift s hs⟩)
        = s - t := by
      show (ConjEtale.eval _).im = s - t
      rw [eval_etaleSec]
      show (ψ (arc (s - t))).im = s - t
      rw [hψarc (s - t) hin, hseg_im]
    rw [this]; ring
  have hprojσ : ∀ s ∈ Set.Ioo a' b', ConjEtale.proj (σ s) ∈ C := by
    intro s hs
    have hin : s - t ∈ Set.Ioo a b := hshiftmem s hs
    show ConjEtale.proj (shift t (Pf s)) ∈ C
    rw [proj_shift, hPeq s (hshift s hs), proj_etaleSec]
    exact hsubC (harc_mem (s - t) hin)
  have hcontσ : ContinuousOn σ (Set.Ioo a' b') := by
    rw [continuousOn_iff_continuous_restrict]
    have hcont1 : Continuous (fun z : ↥(Set.Ioo a' b') =>
        (⟨arc (z.1 - t), hshift z.1 z.2⟩ : ↥(W ∩ Y))) := by
      apply Continuous.subtype_mk
      have hsub : Continuous (fun z : ↥(Set.Ioo a' b') => z.1 - t) :=
        continuous_subtype_val.sub continuous_const
      exact hcont_arc.comp_continuous hsub (fun z => hshiftmem z.1 z.2)
    have hEq : Set.restrict (Set.Ioo a' b') σ
        = fun z => shift t (etaleSec hWYo Set.inter_subset_right hψconj
            ⟨arc (z.1 - t), hshift z.1 z.2⟩) := by
      funext z
      show shift t (Pf z.1) = _
      rw [hPeq z.1 (hshift z.1 z.2)]
    rw [hEq]
    exact (continuous_shift t).comp ((continuous_etaleSec hWYo _ hψconj).comp hcont1)
  -- the section passes through `q`
  have hσq : σ (evIm q) = q := by
    have hzmemab : z.im ∈ Set.Ioo a b := by
      rw [abs_lt] at hzim_bd
      exact ⟨by rw [ha]; linarith [hzim_bd.1], by rw [hb]; linarith [hzim_bd.2]⟩
    have hin : evIm q - t ∈ Set.Ioo a b := by
      have he : evIm q - t = z.im := by rw [hevq]; ring
      rw [he]; exact hzmemab
    have hmem : arc (evIm q - t) ∈ W ∩ Y := harc_WY _ hin
    have harceq : arc (evIm q - t) = y := by
      have he : evIm q - t = z.im := by rw [hevq]; ring
      rw [he]
      show ψ.symm (seg z.im) = y
      have hsz : seg z.im = z :=
        Complex.ext (by rw [hseg_re]; exact hzre.symm) (by rw [hseg_im])
      rw [hsz]; exact hyz
    show shift t (Pf (evIm q)) = q
    rw [hPeq (evIm q) hmem]
    refine ConjEtale.injOn_proj_sheet (V := Set.univ)
      (F := fun x => ψ x + (t : ℂ) * Complex.I) ?_ ?_ harceq
    · refine ⟨Set.mem_univ _, ?_⟩
      show Filter.Germ.map (fun z => z + (t : ℂ) * Complex.I)
          ((fun x => ψ x : Filter.Germ (𝓝 (arc (evIm q - t))) ℂ))
        = ((fun x => ψ x + (t : ℂ) * Complex.I : X → ℂ) :
            Filter.Germ (𝓝 (arc (evIm q - t))) ℂ)
      rw [Filter.Germ.map_coe]; rfl
    · refine ⟨Set.mem_univ _, ?_⟩
      rw [hgerm]
      exact Filter.Germ.coe_eq.mpr ht'
  -- `evIm q` lies in the section interval
  have hevq_mem : evIm q ∈ Set.Ioo a' b' := by
    rw [abs_lt] at hzim_bd
    refine ⟨?_, ?_⟩
    · rw [ha', ha, hevq]; linarith [hzim_bd.1]
    · rw [hb', hb, hevq]; linarith [hzim_bd.2]
  -- the section image lies in the fibre component of `q`
  have himgsub : σ '' Set.Ioo a' b' ⊆
      connectedComponentIn (ConjEtale.proj ⁻¹' C) q := by
    have hpre2 : IsPreconnected (σ '' Set.Ioo a' b') := isPreconnected_Ioo.image σ hcontσ
    have hqin : q ∈ σ '' Set.Ioo a' b' := ⟨evIm q, hevq_mem, hσq⟩
    have hsubP : σ '' Set.Ioo a' b' ⊆ ConjEtale.proj ⁻¹' C := by
      rintro _ ⟨s, hs, rfl⟩; exact hprojσ s hs
    exact hpre2.subset_connectedComponentIn hqin hsubP
  -- the margin interval is inside the section interval
  have hmargin : Set.Ioo (evIm q - ε / 2) (evIm q + ε / 2) ⊆ Set.Ioo a' b' := by
    rw [abs_lt] at hzim_bd
    apply Set.Ioo_subset_Ioo
    · rw [ha', ha, hevq]; linarith [hzim_bd.1]
    · rw [hb', hb, hevq]; linarith [hzim_bd.2]
  intro s hs
  have hsab' : s ∈ Set.Ioo a' b' := hmargin hs
  exact ⟨σ s, himgsub ⟨s, hsab', rfl⟩, hevσ s hsab'⟩

set_option maxHeartbeats 1600000 in
include hVo hdich hfc hchart hYo hCY in
/-- **Surjectivity of `evIm` on the fibre component (Checkpoint B).**  The image
`evIm '' Ê` of the fibre component is all of `ℝ`.  Compactness of the frontier
component `C` gives (finite cover by margin boxes) a *uniform* positive margin
`ℓ`: every achieved value `v` continues to `(v−ℓ, v+ℓ) ⊆ evIm '' Ê`.  Hence the
image is clopen and nonempty in the connected line `ℝ`, so it is everything. -/
theorem evIm_image_component_eq_univ (hVcl : IsCompact (closure V))
    {q₀ : ConjEtale f Y}
    (hq₀ : ConjEtale.proj q₀ ∈ connectedComponentIn (frontier V) x₀) :
    evIm '' connectedComponentIn
      (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀ = Set.univ := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  set Ê := connectedComponentIn (ConjEtale.proj ⁻¹' C) q₀ with hÊ
  have hq₀E : q₀ ∈ Ê := mem_connectedComponentIn hq₀
  set S := evIm '' Ê with hS
  -- cover `C` by the margin boxes
  choose! O r hOopen hξO hrpos hmarginprop using
    fun ξ (hξ : ξ ∈ C) => margin_at hVo hdich hfc hchart hYo hCY hξ
  have hcov : C ⊆ ⋃ ξ ∈ C, O ξ := fun η hη => Set.mem_biUnion hη (hξO η hη)
  obtain ⟨T, hTsub, hTfin, hTcov⟩ :=
    (isCompact_component hVcl (x₀ := x₀)).elim_finite_subcover_image hOopen hcov
  -- a uniform positive margin `ℓ`
  have hTne : T.Nonempty := by
    obtain ⟨ξ, hξT, -⟩ := Set.mem_iUnion₂.mp (hTcov hq₀)
    exact ⟨ξ, hξT⟩
  have hTfne : hTfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hTfin).mpr hTne
  set ℓ := hTfin.toFinset.inf' hTfne r with hℓ
  have hℓpos : 0 < ℓ := by
    rw [hℓ, Finset.lt_inf'_iff]
    intro ξ hξ
    exact hrpos ξ (hTsub ((hTfin.mem_toFinset).mp hξ))
  have hℓle : ∀ ξ ∈ T, ℓ ≤ r ξ := fun ξ hξT =>
    Finset.inf'_le r ((hTfin.mem_toFinset).mpr hξT)
  -- the uniform margin property
  have hmarg : ∀ v ∈ S, Set.Ioo (v - ℓ) (v + ℓ) ⊆ S := by
    rintro v ⟨q, hqE, rfl⟩
    have hqE' : q ∈ connectedComponentIn (ConjEtale.proj ⁻¹' C) q₀ := hÊ ▸ hqE
    have hqP : ConjEtale.proj q ∈ C :=
      Set.mem_preimage.mp (connectedComponentIn_subset (ConjEtale.proj ⁻¹' C) q₀ hqE')
    obtain ⟨ξ, hξT, hqOξ⟩ := Set.mem_iUnion₂.mp (hTcov hqP)
    have hcomp_eq : connectedComponentIn (ConjEtale.proj ⁻¹' C) q = Ê := by
      rw [hÊ]; exact (connectedComponentIn_eq hqE').symm
    have hsub1 : Set.Ioo (evIm q - r ξ) (evIm q + r ξ) ⊆ S := by
      have hmp := hmarginprop ξ (hTsub hξT) q hqOξ hqP
      rw [hcomp_eq, ← hS] at hmp
      exact hmp
    intro w hw
    exact hsub1 (Set.Ioo_subset_Ioo (by linarith [hℓle ξ hξT]) (by linarith [hℓle ξ hξT]) hw)
  -- `S` is clopen and nonempty in the connected line `ℝ`
  have hSne : S.Nonempty := ⟨evIm q₀, q₀, hq₀E, rfl⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro v hv
    exact Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds (⟨by linarith [hℓpos], by linarith [hℓpos]⟩ :
        v ∈ Set.Ioo (v - ℓ) (v + ℓ))) (hmarg v hv)
  have hScompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro v hv
    refine Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds (⟨by linarith [hℓpos], by linarith [hℓpos]⟩ :
        v ∈ Set.Ioo (v - ℓ) (v + ℓ))) ?_
    intro w hw hwS
    exact hv (hmarg w hwS ⟨by linarith [hw.2], by linarith [hw.1]⟩)
  have hSclopen : IsClopen S := ⟨isOpen_compl_iff.mp hScompl, hSopen⟩
  exact hSclopen.eq_univ hSne

end LocalInj

end Uniformization
