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
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
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
    simp only [etaleSec, Set.mem_preimage, ConjEtale.sheet, Set.mem_ofPred_eq, Set.mem_inter_iff]
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
  simp only [ConjEtale.sheet, Set.mem_ofPred_eq]
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
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont1 : Continuous (fun z : ↥(Set.Ioo a' b') =>
        (⟨arc (z.1 - t), hshift z.1 z.2⟩ : ↥(W ∩ Y))) := by
      apply Continuous.subtype_mk
      have hsub : Continuous (fun z : ↥(Set.Ioo a' b') => z.1 - t) :=
        continuous_subtype_val.sub continuous_const
      exact hcont_arc.comp_continuous hsub (fun z => hshiftmem z.1 z.2)
    have hEq : Set.domRestrict (Set.Ioo a' b') σ
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
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
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
  have : T2Space (ConjEtale f Y) := ConjEtale.t2Space
  have : PreconnectedSpace ↥J := Subtype.preconnectedSpace hJ
  have hcont₁ : Continuous (J.domRestrict s₁) := continuousOn_iff_continuous_domRestrict.mp hc₁
  have hcont₂ : Continuous (J.domRestrict s₂) := continuousOn_iff_continuous_domRestrict.mp hc₂
  set E : Set ↥J := {t | J.domRestrict s₁ t = J.domRestrict s₂ t} with hE
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
    have hpre₁ : J.domRestrict s₁ ⁻¹' U ∈ 𝓝 t₀' :=
      hcont₁.continuousAt.preimage_mem_nhds (hUo.mem_nhds hqU)
    have hpre₂ : J.domRestrict s₂ ⁻¹' U ∈ 𝓝 t₀' :=
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
        ∃ σ : ℝ → ConjEtale f Y,
          ContinuousOn σ (Set.Ioo (evIm q - r) (evIm q + r)) ∧
          σ (evIm q) = q ∧
          (∀ s ∈ Set.Ioo (evIm q - r) (evIm q + r), evIm (σ s) = s) ∧
          (∀ s ∈ Set.Ioo (evIm q - r) (evIm q + r),
            ConjEtale.proj (σ s) ∈ connectedComponentIn (frontier V) x₀) ∧
          ∃ U : Set X, IsOpen U ∧ ConjEtale.proj q ∈ U ∧
            ∀ y ∈ connectedComponentIn (frontier V) x₀ ∩ U,
              ∃ s ∈ Set.Ioo (evIm q - r) (evIm q + r), ConjEtale.proj (σ s) = y := by
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
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont1 : Continuous (fun z : ↥(Set.Ioo a' b') =>
        (⟨arc (z.1 - t), hshift z.1 z.2⟩ : ↥(W ∩ Y))) := by
      apply Continuous.subtype_mk
      have hsub : Continuous (fun z : ↥(Set.Ioo a' b') => z.1 - t) :=
        continuous_subtype_val.sub continuous_const
      exact hcont_arc.comp_continuous hsub (fun z => hshiftmem z.1 z.2)
    have hEq : Set.domRestrict (Set.Ioo a' b') σ
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
  -- the margin interval is inside the section interval
  have hmargin : Set.Ioo (evIm q - ε / 2) (evIm q + ε / 2) ⊆ Set.Ioo a' b' := by
    rw [abs_lt] at hzim_bd
    apply Set.Ioo_subset_Ioo
    · rw [ha', ha, hevq]; linarith [hzim_bd.1]
    · rw [hb', hb, hevq]; linarith [hzim_bd.2]
  -- exact projection formula for the section
  have hprojσ_eq : ∀ s ∈ Set.Ioo a' b', ConjEtale.proj (σ s) = arc (s - t) := by
    intro s hs
    show ConjEtale.proj (shift t (Pf s)) = arc (s - t)
    rw [proj_shift, hPeq s (hshift s hs), proj_etaleSec]
  refine ⟨σ, hcontσ.mono hmargin, hσq,
    fun s hs => hevσ s (hmargin hs), fun s hs => hprojσ s (hmargin hs), ?_⟩
  -- the arc-neighbourhood coverage clause: the small box at `z` is traced by `σ`
  have hbox_z : straightBox z c δ (ε / 2) ⊆ box := by
    intro w hw
    rw [mem_straightBox] at hw
    rw [hbox, mem_straightBox]
    refine ⟨hw.1, ?_⟩
    rw [← hm]
    calc |w.im - m| = |(w.im - z.im) + (z.im - m)| := by congr 1; ring
      _ ≤ |w.im - z.im| + |z.im - m| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hw.2 hzim_bd
      _ = ε := by ring
  have hbox_z_tgt : straightBox z c δ (ε / 2) ⊆ ψ.target := hbox_z.trans hbox_tgt
  have hUopen : IsOpen (ψ.symm '' straightBox z c δ (ε / 2)) :=
    ψ.symm.isOpen_image_of_subset_source (isOpen_straightBox _ _ _ _)
      (by rw [OpenPartialHomeomorph.symm_source]; exact hbox_z_tgt)
  have hzmem : z ∈ straightBox z c δ (ε / 2) := by
    rw [mem_straightBox]
    exact ⟨by rw [hzre, sub_self, abs_zero]; exact hδ,
           by rw [sub_self, abs_zero]; exact half_pos hε⟩
  refine ⟨ψ.symm '' straightBox z c δ (ε / 2), hUopen, ⟨z, hzmem, hyz⟩, ?_⟩
  rintro y' ⟨hy'C, w, hw_z, rfl⟩
  have hwbox : w ∈ box := hbox_z hw_z
  have hy'fr : ψ.symm w ∈ frontier V := connectedComponentIn_subset _ _ hy'C
  have hwre : w.re = c := by
    have h1 : f (ψ.symm w) = w.re := hf_eq w hwbox
    rw [← h1]; exact hfc _ hy'fr
  rw [mem_straightBox] at hw_z
  have hw_z2 := abs_lt.mp hw_z.2
  have hs_mem : w.im + t ∈ Set.Ioo (evIm q - ε / 2) (evIm q + ε / 2) := by
    constructor
    · rw [hevq]; linarith [hw_z2.1]
    · rw [hevq]; linarith [hw_z2.2]
  refine ⟨w.im + t, hs_mem, ?_⟩
  rw [hprojσ_eq _ (hmargin hs_mem)]
  have h4 : w.im + t - t = w.im := by ring
  rw [h4]
  show ψ.symm (seg w.im) = ψ.symm w
  congr 1
  apply Complex.ext
  · rw [hseg_re, hwre]
  · rw [hseg_im]

set_option maxHeartbeats 1600000 in
include hVo hdich hfc hchart hYo hCY in
/-- **Uniform section over the whole frontier fibre (Checkpoint C1).**  Compactness
of `C` gives a single positive margin `ℓ` and, through every fibre point `q` over
`C`, a continuous straightening section over `(evIm q − ℓ, evIm q + ℓ)`.  This is
the finite-cover heart of the reachability/gluing construction of the global
section (and of surjectivity). -/
theorem exists_uniform_section (hVcl : IsCompact (closure V))
    (hCne : (connectedComponentIn (frontier V) x₀).Nonempty) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ q : ConjEtale f Y,
      ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀ →
      ∃ σ : ℝ → ConjEtale f Y,
        ContinuousOn σ (Set.Ioo (evIm q - ℓ) (evIm q + ℓ)) ∧
        σ (evIm q) = q ∧
        (∀ s ∈ Set.Ioo (evIm q - ℓ) (evIm q + ℓ), evIm (σ s) = s) ∧
        (∀ s ∈ Set.Ioo (evIm q - ℓ) (evIm q + ℓ),
          ConjEtale.proj (σ s) ∈ connectedComponentIn (frontier V) x₀) := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  choose! O r hOopen hξO hrpos hsecprop using
    fun ξ (hξ : ξ ∈ C) => margin_at hVo hdich hfc hchart hYo hCY hξ
  have hcov : C ⊆ ⋃ ξ ∈ C, O ξ := fun η hη => Set.mem_biUnion hη (hξO η hη)
  obtain ⟨T, hTsub, hTfin, hTcov⟩ :=
    (isCompact_component hVcl (x₀ := x₀)).elim_finite_subcover_image hOopen hcov
  have hTne : T.Nonempty := by
    obtain ⟨ξ, hξ⟩ := hCne
    obtain ⟨ζ, hζT, -⟩ := Set.mem_iUnion₂.mp (hTcov hξ)
    exact ⟨ζ, hζT⟩
  have hTfne : hTfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hTfin).mpr hTne
  set ℓ := hTfin.toFinset.inf' hTfne r with hℓ
  have hℓpos : 0 < ℓ := by
    rw [hℓ, Finset.lt_inf'_iff]
    intro ξ hξ
    exact hrpos ξ (hTsub ((hTfin.mem_toFinset).mp hξ))
  have hℓle : ∀ ξ ∈ T, ℓ ≤ r ξ := fun ξ hξT =>
    Finset.inf'_le r ((hTfin.mem_toFinset).mpr hξT)
  refine ⟨ℓ, hℓpos, ?_⟩
  intro q hqC
  obtain ⟨ξ, hξT, hqOξ⟩ := Set.mem_iUnion₂.mp (hTcov hqC)
  obtain ⟨σ, hcont, hσq, hev, hproj, -⟩ := hsecprop ξ (hTsub hξT) q hqOξ hqC
  have hsub : Set.Ioo (evIm q - ℓ) (evIm q + ℓ) ⊆ Set.Ioo (evIm q - r ξ) (evIm q + r ξ) :=
    Set.Ioo_subset_Ioo (by linarith [hℓle ξ hξT]) (by linarith [hℓle ξ hξT])
  exact ⟨σ, hcont.mono hsub, hσq, fun s hs => hev s (hsub hs), fun s hs => hproj s (hsub hs)⟩

include hVo hdich hfc hchart hYo hCY in
/-- **Uniform margin (image form).**  From the uniform section, every fibre point
`q` over `C` has `(evIm q − ℓ, evIm q + ℓ) ⊆ evIm '' (fibre component of `q`)`. -/
theorem exists_uniform_margin (hVcl : IsCompact (closure V))
    (hCne : (connectedComponentIn (frontier V) x₀).Nonempty) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ q : ConjEtale f Y,
      ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀ →
      Set.Ioo (evIm q - ℓ) (evIm q + ℓ) ⊆
        evIm '' connectedComponentIn
          (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q := by
  obtain ⟨ℓ, hℓpos, hsec⟩ := exists_uniform_section hVo hdich hfc hchart hYo hCY hVcl hCne
  refine ⟨ℓ, hℓpos, ?_⟩
  intro q hqC
  obtain ⟨σ, hcont, hσq, hev, hproj⟩ := hsec q hqC
  have himg : σ '' Set.Ioo (evIm q - ℓ) (evIm q + ℓ) ⊆
      connectedComponentIn (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q := by
    have hpre := isPreconnected_Ioo.image σ hcont
    have hqin : q ∈ σ '' Set.Ioo (evIm q - ℓ) (evIm q + ℓ) :=
      ⟨evIm q, ⟨by linarith [hℓpos], by linarith [hℓpos]⟩, hσq⟩
    have hsubP : σ '' Set.Ioo (evIm q - ℓ) (evIm q + ℓ) ⊆
        ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀ := by
      rintro _ ⟨s, hs, rfl⟩; exact hproj s hs
    exact hpre.subset_connectedComponentIn hqin hsubP
  intro w hw
  exact ⟨σ w, himg ⟨w, hw, rfl⟩, hev w hw⟩

include hVo hdich hfc hchart hYo hCY in
/-- **Surjectivity of `evIm` on the fibre component (Checkpoint B).**  The image
`evIm '' Ê` of the fibre component is all of `ℝ`.  Compactness of the frontier
component `C` gives a *uniform* positive margin `ℓ`: every achieved value `v`
continues to `(v−ℓ, v+ℓ) ⊆ evIm '' Ê`.  Hence the image is clopen and nonempty in
the connected line `ℝ`, so it is everything. -/
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
  obtain ⟨ℓ, hℓpos, hmarg0⟩ :=
    exists_uniform_margin hVo hdich hfc hchart hYo hCY hVcl ⟨ConjEtale.proj q₀, hq₀⟩
  -- the uniform margin property, transported into `S`
  have hmarg : ∀ v ∈ S, Set.Ioo (v - ℓ) (v + ℓ) ⊆ S := by
    rintro v ⟨q, hqE, rfl⟩
    have hqE' : q ∈ connectedComponentIn (ConjEtale.proj ⁻¹' C) q₀ := hÊ ▸ hqE
    have hqP : ConjEtale.proj q ∈ C :=
      Set.mem_preimage.mp (connectedComponentIn_subset (ConjEtale.proj ⁻¹' C) q₀ hqE')
    have hcomp_eq : connectedComponentIn (ConjEtale.proj ⁻¹' C) q = Ê := by
      rw [hÊ]; exact (connectedComponentIn_eq hqE').symm
    have hmp := hmarg0 q hqP
    rw [hcomp_eq, ← hS] at hmp
    exact hmp
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

/-! ### Checkpoint C2 — the global section by clopen reachability -/

/-- **Reachability extension step (C2 core).**  A continuous straightening section
of `evIm` over the symmetric closed interval `[v₀−n, v₀+n]` (through `q₀`, landing
in `C`) extends to radius `n + ℓ/2`, by gluing the uniform-margin sections at the
two endpoints.  The uniform section input `hsec` is `exists_uniform_section`, so
`ℓ` is fixed across all extension steps.  We require `0 < n` so the two endpoint
sections do not overlap (edge case handled by starting induction at radius `ℓ/2`). -/
theorem reach_extend {q₀ : ConjEtale f Y} {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hsec : ∀ q : ConjEtale f Y,
      ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀ →
      ∃ σ : ℝ → ConjEtale f Y,
        ContinuousOn σ (Set.Ioo (evIm q - ℓ) (evIm q + ℓ)) ∧
        σ (evIm q) = q ∧
        (∀ s ∈ Set.Ioo (evIm q - ℓ) (evIm q + ℓ), evIm (σ s) = s) ∧
        (∀ s ∈ Set.Ioo (evIm q - ℓ) (evIm q + ℓ),
          ConjEtale.proj (σ s) ∈ connectedComponentIn (frontier V) x₀))
    {v₀ n : ℝ} (hv₀ : evIm q₀ = v₀) (hn : 0 < n)
    (hR : ∃ σ : ℝ → ConjEtale f Y,
      ContinuousOn σ (Set.Icc (v₀ - n) (v₀ + n)) ∧
      (∀ u ∈ Set.Icc (v₀ - n) (v₀ + n), evIm (σ u) = u) ∧
      (∀ u ∈ Set.Icc (v₀ - n) (v₀ + n),
        ConjEtale.proj (σ u) ∈ connectedComponentIn (frontier V) x₀) ∧
      σ v₀ = q₀) :
    ∃ σ : ℝ → ConjEtale f Y,
      ContinuousOn σ (Set.Icc (v₀ - (n + ℓ / 2)) (v₀ + (n + ℓ / 2))) ∧
      (∀ u ∈ Set.Icc (v₀ - (n + ℓ / 2)) (v₀ + (n + ℓ / 2)), evIm (σ u) = u) ∧
      (∀ u ∈ Set.Icc (v₀ - (n + ℓ / 2)) (v₀ + (n + ℓ / 2)),
        ConjEtale.proj (σ u) ∈ connectedComponentIn (frontier V) x₀) ∧
      σ v₀ = q₀ := by
  classical
  obtain ⟨σ, hσcont, hσev, hσproj, hσv₀⟩ := hR
  have hmemL : v₀ - n ∈ Set.Icc (v₀ - n) (v₀ + n) := ⟨le_refl _, by linarith⟩
  have hmemR : v₀ + n ∈ Set.Icc (v₀ - n) (v₀ + n) := ⟨by linarith, le_refl _⟩
  have hLproj : ConjEtale.proj (σ (v₀ - n)) ∈ connectedComponentIn (frontier V) x₀ :=
    hσproj _ hmemL
  have hLev : evIm (σ (v₀ - n)) = v₀ - n := hσev _ hmemL
  have hRproj : ConjEtale.proj (σ (v₀ + n)) ∈ connectedComponentIn (frontier V) x₀ :=
    hσproj _ hmemR
  have hRev : evIm (σ (v₀ + n)) = v₀ + n := hσev _ hmemR
  obtain ⟨σL, hσLcont, hσLq, hσLev, hσLproj⟩ := hsec _ hLproj
  obtain ⟨σR, hσRcont, hσRq, hσRev, hσRproj⟩ := hsec _ hRproj
  rw [hLev] at hσLcont hσLq hσLev hσLproj
  rw [hRev] at hσRcont hσRq hσRev hσRproj
  -- the glued section
  refine ⟨fun u => if u ≤ v₀ - n then σL u else if u ≤ v₀ + n then σ u else σR u,
    ?_, ?_, ?_, ?_⟩
  · -- continuity, by gluing on three closed pieces
    have hbig : Set.Icc (v₀ - (n + ℓ / 2)) (v₀ + (n + ℓ / 2))
        = (Set.Icc (v₀ - (n + ℓ / 2)) (v₀ - n) ∪ Set.Icc (v₀ - n) (v₀ + n))
          ∪ Set.Icc (v₀ + n) (v₀ + (n + ℓ / 2)) := by
      rw [Set.Icc_union_Icc_eq_Icc (by linarith) (by linarith),
        Set.Icc_union_Icc_eq_Icc (by linarith) (by linarith)]
    rw [hbig]
    have hgIL : ContinuousOn (fun u => if u ≤ v₀ - n then σL u else
        if u ≤ v₀ + n then σ u else σR u) (Set.Icc (v₀ - (n + ℓ / 2)) (v₀ - n)) := by
      refine (hσLcont.mono ?_).congr ?_
      · intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · intro u hu
        show (if u ≤ v₀ - n then σL u else _) = σL u
        rw [if_pos hu.2]
    have hgIM : ContinuousOn (fun u => if u ≤ v₀ - n then σL u else
        if u ≤ v₀ + n then σ u else σR u) (Set.Icc (v₀ - n) (v₀ + n)) := by
      refine hσcont.congr ?_
      intro u hu
      show (if u ≤ v₀ - n then σL u else if u ≤ v₀ + n then σ u else σR u) = σ u
      by_cases hle : u ≤ v₀ - n
      · have hueq : u = v₀ - n := le_antisymm hle hu.1
        rw [if_pos hle, hueq, hσLq]
      · rw [if_neg hle, if_pos hu.2]
    have hgIR : ContinuousOn (fun u => if u ≤ v₀ - n then σL u else
        if u ≤ v₀ + n then σ u else σR u) (Set.Icc (v₀ + n) (v₀ + (n + ℓ / 2))) := by
      refine (hσRcont.mono ?_).congr ?_
      · intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · intro u hu
        show (if u ≤ v₀ - n then σL u else if u ≤ v₀ + n then σ u else σR u) = σR u
        have hle : ¬ u ≤ v₀ - n := by push Not; linarith [hu.1]
        by_cases hle2 : u ≤ v₀ + n
        · have hueq : u = v₀ + n := le_antisymm hle2 hu.1
          rw [if_neg hle, if_pos hle2, hueq, hσRq]
        · rw [if_neg hle, if_neg hle2]
    exact (hgIL.union_of_isClosed hgIM isClosed_Icc isClosed_Icc).union_of_isClosed
      hgIR (isClosed_Icc.union isClosed_Icc) isClosed_Icc
  · -- evIm ∘ section = id
    intro u hu
    show evIm (if u ≤ v₀ - n then σL u else if u ≤ v₀ + n then σ u else σR u) = u
    by_cases hle : u ≤ v₀ - n
    · rw [if_pos hle]
      exact hσLev u ⟨by linarith [hu.1], by linarith⟩
    · rw [if_neg hle]
      by_cases hle2 : u ≤ v₀ + n
      · rw [if_pos hle2]; push Not at hle; exact hσev u ⟨le_of_lt hle, hle2⟩
      · rw [if_neg hle2]; push Not at hle2; exact hσRev u ⟨by linarith, by linarith [hu.2]⟩
  · -- projection lands in `C`
    intro u hu
    show ConjEtale.proj (if u ≤ v₀ - n then σL u else if u ≤ v₀ + n then σ u else σR u)
      ∈ connectedComponentIn (frontier V) x₀
    by_cases hle : u ≤ v₀ - n
    · rw [if_pos hle]
      exact hσLproj u ⟨by linarith [hu.1], by linarith⟩
    · rw [if_neg hle]
      by_cases hle2 : u ≤ v₀ + n
      · rw [if_pos hle2]; push Not at hle; exact hσproj u ⟨le_of_lt hle, hle2⟩
      · rw [if_neg hle2]; push Not at hle2; exact hσRproj u ⟨by linarith, by linarith [hu.2]⟩
  · -- value at `v₀`
    show (if v₀ ≤ v₀ - n then σL v₀ else if v₀ ≤ v₀ + n then σ v₀ else σR v₀) = q₀
    rw [if_neg (by linarith), if_pos (by linarith)]; exact hσv₀

include hVo hdich hfc hchart hYo hCY in
/-- **Reachability at every radius (C2).**  Through `q₀` there is, for every radius
`N`, a continuous straightening section of `evIm` over `[evIm q₀ − N, evIm q₀ + N]`
landing in `C`.  Proved by induction from radius `ℓ/2` using `reach_extend`, then
downward closure. -/
theorem reach_all (hVcl : IsCompact (closure V)) {q₀ : ConjEtale f Y}
    (hq₀ : ConjEtale.proj q₀ ∈ connectedComponentIn (frontier V) x₀) (N : ℝ) :
    ∃ σ : ℝ → ConjEtale f Y,
      ContinuousOn σ (Set.Icc (evIm q₀ - N) (evIm q₀ + N)) ∧
      (∀ u ∈ Set.Icc (evIm q₀ - N) (evIm q₀ + N), evIm (σ u) = u) ∧
      (∀ u ∈ Set.Icc (evIm q₀ - N) (evIm q₀ + N),
        ConjEtale.proj (σ u) ∈ connectedComponentIn (frontier V) x₀) ∧
      σ (evIm q₀) = q₀ := by
  classical
  obtain ⟨ℓ, hℓpos, hsec⟩ :=
    exists_uniform_section hVo hdich hfc hchart hYo hCY hVcl ⟨_, hq₀⟩
  let Reach : ℝ → Prop := fun r => ∃ σ : ℝ → ConjEtale f Y,
    ContinuousOn σ (Set.Icc (evIm q₀ - r) (evIm q₀ + r)) ∧
    (∀ u ∈ Set.Icc (evIm q₀ - r) (evIm q₀ + r), evIm (σ u) = u) ∧
    (∀ u ∈ Set.Icc (evIm q₀ - r) (evIm q₀ + r),
      ConjEtale.proj (σ u) ∈ connectedComponentIn (frontier V) x₀) ∧ σ (evIm q₀) = q₀
  have hdown : ∀ m r : ℝ, r ≤ m → Reach m → Reach r := by
    intro m r hrm hPm
    obtain ⟨σ, hcont, hev, hproj, hv⟩ := hPm
    have hsub : Set.Icc (evIm q₀ - r) (evIm q₀ + r) ⊆
        Set.Icc (evIm q₀ - m) (evIm q₀ + m) :=
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact ⟨σ, hcont.mono hsub, fun u hu => hev u (hsub hu), fun u hu => hproj u (hsub hu), hv⟩
  have hbase : Reach (ℓ / 2) := by
    obtain ⟨σ, hcont, hσq, hev, hproj⟩ := hsec q₀ hq₀
    refine ⟨σ, hcont.mono ?_, fun u hu => hev u ?_, fun u hu => hproj u ?_, hσq⟩
    · exact fun u hu => ⟨by linarith [hu.1, hℓpos], by linarith [hu.2, hℓpos]⟩
    · exact ⟨by linarith [hu.1, hℓpos], by linarith [hu.2, hℓpos]⟩
    · exact ⟨by linarith [hu.1, hℓpos], by linarith [hu.2, hℓpos]⟩
  have hind : ∀ k : ℕ, Reach (((k : ℝ) + 1) * (ℓ / 2)) := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      have hn : 0 < ((k : ℝ) + 1) * (ℓ / 2) := by positivity
      have hext := reach_extend hℓpos hsec (v₀ := evIm q₀) (n := ((k : ℝ) + 1) * (ℓ / 2))
        rfl hn ih
      have harith : ((↑(k + 1) : ℝ) + 1) * (ℓ / 2) = ((k : ℝ) + 1) * (ℓ / 2) + ℓ / 2 := by
        push_cast; ring
      rw [harith]
      exact hext
  by_cases hN : N ≤ ℓ / 2
  · exact hdown (ℓ / 2) N hN hbase
  · obtain ⟨k, hk⟩ := exists_nat_ge (N / (ℓ / 2))
    have hbig : N ≤ ((k : ℝ) + 1) * (ℓ / 2) := by
      have h1 : N ≤ (k : ℝ) * (ℓ / 2) := (div_le_iff₀ (half_pos hℓpos)).mp hk
      have h2 : ((k : ℝ) + 1) * (ℓ / 2) = (k : ℝ) * (ℓ / 2) + ℓ / 2 := by ring
      linarith [half_pos hℓpos]
    exact hdown (((k : ℝ) + 1) * (ℓ / 2)) N hbig (hind k)

/-! ### Checkpoint C3 — injectivity and the continuous inverse -/

include hVo hdich hfc hchart hYo hCY in
/-- **Continuous inverse and injectivity of `evIm` on `Ê` (Checkpoint C3).**  From
the global reachability sections we assemble a continuous global section
`E : ℝ → Ê` of `evIm` through `q₀`; its image is clopen in the connected fibre
component `Ê`, hence all of `Ê`, whence `evIm` is injective on `Ê` and `E` is its
two-sided inverse. -/
theorem exists_evIm_inverse (hVcl : IsCompact (closure V)) {q₀ : ConjEtale f Y}
    (hq₀ : ConjEtale.proj q₀ ∈ connectedComponentIn (frontier V) x₀) :
    ∃ E : ℝ → ConjEtale f Y, Continuous E ∧ (∀ t, evIm (E t) = t) ∧
      (∀ t, E t ∈ connectedComponentIn
        (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀) ∧
      (∀ q ∈ connectedComponentIn
        (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀, E (evIm q) = q) ∧
      Set.InjOn evIm (connectedComponentIn
        (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀) := by
  classical
  have : T2Space (ConjEtale f Y) := ConjEtale.t2Space
  choose F hFcont hFev hFproj hFv₀ using
    reach_all hVo hdich hfc hchart hYo hCY hVcl hq₀
  set v₀ := evIm q₀ with hv₀
  set Ê := connectedComponentIn (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀
    with hÊ
  have hq₀Ê : q₀ ∈ Ê := mem_connectedComponentIn hq₀
  have hÊP : ∀ w, w ∈ Ê → ConjEtale.proj w ∈ connectedComponentIn (frontier V) x₀ :=
    fun w hw => Set.mem_preimage.mp (connectedComponentIn_subset _ _ (hÊ ▸ hw))
  -- interval membership helper
  have hmem : ∀ (N s : ℝ), |s - v₀| ≤ N → s ∈ Set.Icc (v₀ - N) (v₀ + N) := by
    intro N s hs; rw [abs_le] at hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- agreement of witnesses on shared radii
  have hagree : ∀ (N M s : ℝ), s ∈ Set.Icc (v₀ - N) (v₀ + N) →
      s ∈ Set.Icc (v₀ - M) (v₀ + M) → F N s = F M s := by
    intro N M s hsN hsM
    have hN0 : (0 : ℝ) ≤ N := by have := hsN.1; have := hsN.2; linarith
    have hM0 : (0 : ℝ) ≤ M := by have := hsM.1; have := hsM.2; linarith
    have hJN : Set.Icc (min v₀ s) (max v₀ s) ⊆ Set.Icc (v₀ - N) (v₀ + N) :=
      Set.Icc_subset_Icc (le_min (by linarith) hsN.1) (max_le (by linarith) hsN.2)
    have hJM : Set.Icc (min v₀ s) (max v₀ s) ⊆ Set.Icc (v₀ - M) (v₀ + M) :=
      Set.Icc_subset_Icc (le_min (by linarith) hsM.1) (max_le (by linarith) hsM.2)
    have hun := section_unique hVo hdich hfc hchart hYo hCY
      (J := Set.Icc (min v₀ s) (max v₀ s)) isPreconnected_Icc
      ((hFcont N).mono hJN) ((hFcont M).mono hJM)
      (fun t ht => hFev N t (hJN ht)) (fun t ht => hFev M t (hJM ht))
      (fun t ht => hFproj N t (hJN ht)) (fun t ht => hFproj M t (hJM ht))
      (t₀ := v₀) ⟨min_le_left _ _, le_max_left _ _⟩ (by rw [hFv₀ N, hFv₀ M])
    exact hun s ⟨min_le_right _ _, le_max_right _ _⟩
  -- the global section
  set E : ℝ → ConjEtale f Y := fun t => F (|t - v₀| + 1) t with hEdef
  have hrmem : ∀ t, t ∈ Set.Icc (v₀ - (|t - v₀| + 1)) (v₀ + (|t - v₀| + 1)) :=
    fun t => hmem _ t (by linarith)
  have hevE : ∀ t, evIm (E t) = t := fun t => hFev _ t (hrmem t)
  have hEmemÊ : ∀ t, E t ∈ Ê := by
    intro t
    have hpre : IsPreconnected (F (|t - v₀| + 1) ''
        Set.Icc (v₀ - (|t - v₀| + 1)) (v₀ + (|t - v₀| + 1))) :=
      isPreconnected_Icc.image _ (hFcont _)
    have hq₀in : q₀ ∈ F (|t - v₀| + 1) ''
        Set.Icc (v₀ - (|t - v₀| + 1)) (v₀ + (|t - v₀| + 1)) :=
      ⟨v₀, hmem _ v₀ (by rw [sub_self, abs_zero]; positivity), hFv₀ _⟩
    have hsubP : F (|t - v₀| + 1) '' Set.Icc (v₀ - (|t - v₀| + 1)) (v₀ + (|t - v₀| + 1)) ⊆
        ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀ := by
      rintro _ ⟨u, hu, rfl⟩; exact hFproj _ u hu
    exact (hÊ ▸ hpre.subset_connectedComponentIn hq₀in hsubP) ⟨t, hrmem t, rfl⟩
  -- continuity of the global section
  have hEcont : Continuous E := by
    rw [continuous_iff_continuousAt]
    intro w
    have hwint : w ∈ Set.Ioo (v₀ - (|w - v₀| + 1)) (v₀ + (|w - v₀| + 1)) :=
      ⟨by linarith [neg_abs_le (w - v₀)], by linarith [le_abs_self (w - v₀)]⟩
    have hloceq : Set.EqOn E (F (|w - v₀| + 1))
        (Set.Ioo (v₀ - (|w - v₀| + 1)) (v₀ + (|w - v₀| + 1))) := by
      intro s hs
      exact hagree _ _ s (hmem _ s (by linarith)) ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hIcc : Set.Icc (v₀ - (|w - v₀| + 1)) (v₀ + (|w - v₀| + 1)) ∈ 𝓝 w :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hwint) Set.Ioo_subset_Icc_self
    have hcAt : ContinuousAt (F (|w - v₀| + 1)) w := (hFcont _).continuousAt hIcc
    exact hcAt.congr (hloceq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hwint)).symm
  -- the section image is all of `Ê` (clopen in the connected component)
  have himg : ∀ q ∈ Ê, E (evIm q) = q := by
    have hÊpre : IsPreconnected Ê := by rw [hÊ]; exact isPreconnected_connectedComponentIn
    have : PreconnectedSpace ↥Ê := Subtype.preconnectedSpace hÊpre
    set A : Set ↥Ê := {q | E (evIm q.1) = q.1} with hA
    have hAclosed : IsClosed A :=
      isClosed_eq (hEcont.comp (continuous_evIm.comp continuous_subtype_val))
        continuous_subtype_val
    have hAopen : IsOpen A := by
      rw [isOpen_iff_mem_nhds]
      intro q hqA
      have hpP : ConjEtale.proj q.1 ∈ connectedComponentIn (frontier V) x₀ := hÊP _ q.2
      obtain ⟨U, hUo, hpU, hUinj⟩ := exists_evIm_local_inj hVo hdich hfc hchart hYo hCY hpP
      have hEp : E (evIm q.1) = q.1 := hqA
      have hWo : IsOpen (Subtype.val ⁻¹' (U ∩ (fun w => E (evIm w)) ⁻¹' U) : Set ↥Ê) :=
        (hUo.inter ((hEcont.comp continuous_evIm).isOpen_preimage _ hUo)).preimage
          continuous_subtype_val
      have hqW : q ∈ (Subtype.val ⁻¹' (U ∩ (fun w => E (evIm w)) ⁻¹' U) : Set ↥Ê) := by
        refine ⟨hpU, ?_⟩
        show E (evIm q.1) ∈ U
        rw [hEp]; exact hpU
      refine Filter.mem_of_superset (hWo.mem_nhds hqW) ?_
      intro q' hq'
      show E (evIm q'.1) = q'.1
      have h1 : q'.1 ∈ U ∩ (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) :=
        ⟨hq'.1, hÊP _ q'.2⟩
      have h2 : E (evIm q'.1) ∈ U ∩ (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) :=
        ⟨hq'.2, hÊP _ (hEmemÊ (evIm q'.1))⟩
      exact hUinj h2 h1 (hevE (evIm q'.1))
    have hAne : (⟨q₀, hq₀Ê⟩ : ↥Ê) ∈ A := by
      show E (evIm q₀) = q₀
      rw [← hv₀]
      show F (|v₀ - v₀| + 1) v₀ = q₀
      rw [sub_self, abs_zero, zero_add]; exact hFv₀ 1
    have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ ⟨_, hAne⟩
    intro q hq
    have : (⟨q, hq⟩ : ↥Ê) ∈ A := hAuniv ▸ Set.mem_univ _
    exact this
  have hInj : Set.InjOn evIm Ê := by
    intro q hq q' hq' hev
    rw [← himg q hq, ← himg q' hq', hev]
  exact ⟨E, hEcont, hevE, hEmemÊ, himg, hInj⟩

/-! ### Stage 3 — deck transformations and the periodic parametrisation -/

/-- **Fibre transitivity of the deck action.**  Two conjugate germs over the same
base point differ by the imaginary shift of their `evIm`-difference (the real
parts of the evaluations agree automatically, both being `f` at the base). -/
theorem shift_eq_of_proj_eq {q q' : ConjEtale f Y}
    (hproj : ConjEtale.proj q = ConjEtale.proj q') :
    q' = shift (evIm q' - evIm q) q := by
  symm
  apply eq_of_proj_eq_eval_eq
  · rw [proj_shift]; exact hproj
  · rw [eval_shift]
    apply Complex.ext
    · have h1 : ((((evIm q' - evIm q) : ℝ) : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [Complex.add_re, h1, add_zero, re_eval, re_eval, hproj]
    · have h2 : ((((evIm q' - evIm q) : ℝ) : ℂ) * Complex.I).im = evIm q' - evIm q := by
        simp [Complex.mul_im]
      rw [Complex.add_im, h2]
      show evIm q + (evIm q' - evIm q) = evIm q'
      ring

/-- **The deck action permutes fibre components.**  `shift r` is a homeomorphism
preserving the fibre `proj⁻¹ C`, so it maps the component of `q` onto the
component of `shift r q`. -/
theorem shift_image_component (r : ℝ) {q : ConjEtale f Y}
    (hq : ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀) :
    shift r '' connectedComponentIn
        (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q
      = connectedComponentIn
        (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) (shift r q) := by
  have hcoe : ⇑(shiftHomeo (f := f) (Y := Y) r) = shift (f := f) (Y := Y) r := rfl
  have hpre : shiftHomeo (f := f) (Y := Y) r ''
      (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀)
      = ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀ := by
    rw [hcoe]
    apply Set.Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      simp only [Set.mem_preimage, proj_shift]
      exact hp
    · intro p hp
      refine ⟨shift (-r) p, ?_, shift_shift_neg r p⟩
      simp only [Set.mem_preimage, proj_shift]
      exact hp
  have h := (shiftHomeo (f := f) (Y := Y) r).image_connectedComponentIn
    (s := ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) (x := q) hq
  rw [hpre, hcoe] at h
  exact h

include hVo hdich hfc hchart hYo hCY in
/-- **The fibre component projects onto an arc neighbourhood.**  Every fibre point
`q` over the frontier component `C` has an open `U ∋ proj q` such that all of
`C ∩ U` is traced by the local section through `q` (hence lies in the projection
of the fibre component of `q`), with a uniform `evIm`-bound `r`. -/
theorem exists_proj_arc_nbhd {q : ConjEtale f Y}
    (hqC : ConjEtale.proj q ∈ connectedComponentIn (frontier V) x₀) :
    ∃ (r : ℝ) (U : Set X), 0 < r ∧ IsOpen U ∧ ConjEtale.proj q ∈ U ∧
      ∀ y ∈ connectedComponentIn (frontier V) x₀ ∩ U,
        ∃ w ∈ connectedComponentIn
          (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q,
          ConjEtale.proj w = y ∧ |evIm w - evIm q| < r := by
  obtain ⟨O, r, hOo, hqO, hrpos, hprop⟩ := margin_at hVo hdich hfc hchart hYo hCY hqC
  obtain ⟨σ, hcont, hσq, hev, hproj, U, hUo, hqU, hcov⟩ := hprop q hqO hqC
  have himgsub : σ '' Set.Ioo (evIm q - r) (evIm q + r) ⊆
      connectedComponentIn (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q := by
    have hpre := isPreconnected_Ioo.image σ hcont
    have hqin : q ∈ σ '' Set.Ioo (evIm q - r) (evIm q + r) :=
      ⟨evIm q, ⟨by linarith, by linarith⟩, hσq⟩
    have hsubP : σ '' Set.Ioo (evIm q - r) (evIm q + r) ⊆
        ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀ := by
      rintro _ ⟨s, hs, rfl⟩; exact hproj s hs
    exact hpre.subset_connectedComponentIn hqin hsubP
  refine ⟨r, U, hrpos, hUo, hqU, ?_⟩
  intro y hy
  obtain ⟨s, hs, hsy⟩ := hcov y hy
  refine ⟨σ s, himgsub ⟨s, hs, rfl⟩, hsy, ?_⟩
  rw [hev s hs, abs_lt]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

set_option maxHeartbeats 1600000 in
include hVo hdich hfc hchart hYo hCY in
/-- **The fibre component projects onto the whole frontier component.**
Membership in `proj '' Ê` is locally constant on `C` (via arc neighbourhoods and
the transitive deck action on fibres), so `proj '' Ê` is clopen and nonempty in
the connected `C`, hence equal to `C`. -/
theorem proj_image_component_eq (hfY : SurfaceHarmonicOn f Y) {q₀ : ConjEtale f Y}
    (hq₀C : ConjEtale.proj q₀ ∈ connectedComponentIn (frontier V) x₀) :
    ConjEtale.proj '' connectedComponentIn
      (ConjEtale.proj ⁻¹' connectedComponentIn (frontier V) x₀) q₀
    = connectedComponentIn (frontier V) x₀ := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  set Ê := connectedComponentIn (ConjEtale.proj ⁻¹' C) q₀ with hÊ
  have hÊsub : Ê ⊆ ConjEtale.proj ⁻¹' C := connectedComponentIn_subset _ _
  have hsub : ConjEtale.proj '' Ê ⊆ C := by rintro _ ⟨p, hp, rfl⟩; exact hÊsub hp
  -- membership in `proj '' Ê` is locally constant on `C`
  have hloc : ∀ y ∈ C, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧
      ∀ y' ∈ C ∩ U, (y ∈ ConjEtale.proj '' Ê ↔ y' ∈ ConjEtale.proj '' Ê) := by
    intro y hyC
    have hyY : y ∈ Y := hCY hyC
    obtain ⟨q, hqy⟩ := ConjEtale.exists_mk hfY hYo hyY
    have hqC : ConjEtale.proj q ∈ C := by rw [hqy]; exact hyC
    obtain ⟨r, U, hr, hUo, hqU, hcov⟩ :=
      exists_proj_arc_nbhd hVo hdich hfc hchart hYo hCY hqC
    refine ⟨U, hUo, by rw [← hqy]; exact hqU, ?_⟩
    intro y' hy'
    obtain ⟨w, hw, hwy', -⟩ := hcov y' hy'
    constructor
    · rintro ⟨p, hpÊ, hpy⟩
      have hpq : ConjEtale.proj p = ConjEtale.proj q := by rw [hpy, hqy]
      have h1 : q = shift (evIm q - evIm p) p := shift_eq_of_proj_eq hpq
      have hpC : ConjEtale.proj p ∈ C := hÊsub hpÊ
      have h2 : shift (evIm q - evIm p) '' connectedComponentIn (ConjEtale.proj ⁻¹' C) p
          = connectedComponentIn (ConjEtale.proj ⁻¹' C) (shift (evIm q - evIm p) p) :=
        shift_image_component _ hpC
      have hcompp : connectedComponentIn (ConjEtale.proj ⁻¹' C) p = Ê := by
        rw [hÊ]; exact (connectedComponentIn_eq hpÊ).symm
      rw [hcompp, ← h1] at h2
      have hw' : w ∈ shift (evIm q - evIm p) '' Ê := by rw [h2]; exact hw
      obtain ⟨p', hp'Ê, hp'w⟩ := hw'
      exact ⟨p', hp'Ê, by rw [← hwy', ← hp'w, proj_shift]⟩
    · rintro ⟨p', hp'Ê, hp'y'⟩
      have hwp' : ConjEtale.proj w = ConjEtale.proj p' := by rw [hwy', hp'y']
      have h1 : p' = shift (evIm p' - evIm w) w := shift_eq_of_proj_eq hwp'
      have hwC : ConjEtale.proj w ∈ C :=
        Set.mem_preimage.mp (connectedComponentIn_subset (ConjEtale.proj ⁻¹' C) q hw)
      have h2 : shift (evIm p' - evIm w) '' connectedComponentIn (ConjEtale.proj ⁻¹' C) w
          = connectedComponentIn (ConjEtale.proj ⁻¹' C) (shift (evIm p' - evIm w) w) :=
        shift_image_component _ hwC
      have hcompw : connectedComponentIn (ConjEtale.proj ⁻¹' C) w
          = connectedComponentIn (ConjEtale.proj ⁻¹' C) q :=
        (connectedComponentIn_eq hw).symm
      have hcompp' : connectedComponentIn (ConjEtale.proj ⁻¹' C)
          (shift (evIm p' - evIm w) w) = Ê := by
        rw [← h1, hÊ]; exact (connectedComponentIn_eq hp'Ê).symm
      rw [hcompw, hcompp'] at h2
      have hq' : shift (evIm p' - evIm w) q ∈ Ê := by
        rw [← h2]
        exact ⟨q, mem_connectedComponentIn hqC, rfl⟩
      exact ⟨shift (evIm p' - evIm w) q, hq', by rw [proj_shift, hqy]⟩
  -- clopen argument in the connected subtype `↥C`
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have : PreconnectedSpace ↥C := Subtype.preconnectedSpace hCpre
  set S : Set ↥C := Subtype.val ⁻¹' (ConjEtale.proj '' Ê) with hSdef
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨y, hyC⟩ hyS
    obtain ⟨U, hUo, hyU, hiff⟩ := hloc y hyC
    refine Filter.mem_of_superset
      ((hUo.preimage continuous_subtype_val).mem_nhds hyU) ?_
    rintro ⟨y', hy'C⟩ hy'U
    exact (hiff y' ⟨hy'C, hy'U⟩).mp hyS
  have hScompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨y, hyC⟩ hyS
    obtain ⟨U, hUo, hyU, hiff⟩ := hloc y hyC
    refine Filter.mem_of_superset
      ((hUo.preimage continuous_subtype_val).mem_nhds hyU) ?_
    rintro ⟨y', hy'C⟩ hy'U hy'S
    exact hyS ((hiff y' ⟨hy'C, hy'U⟩).mpr hy'S)
  have hSne : S.Nonempty :=
    ⟨⟨ConjEtale.proj q₀, hq₀C⟩, ⟨q₀, mem_connectedComponentIn hq₀C, rfl⟩⟩
  have huniv := IsClopen.eq_univ ⟨isOpen_compl_iff.mp hScompl, hSopen⟩ hSne
  apply Set.Subset.antisymm hsub
  intro y hyC
  have : (⟨y, hyC⟩ : ↥C) ∈ S := huniv ▸ Set.mem_univ _
  exact this

set_option maxHeartbeats 1600000 in
include hVo hdich hfc hchart hYo hCY in
/-- **Periodic parametrisation, collar form (Stage 3).**  Given the collar data
over `Y ⊇ C` and compactness of `closure V`, the frontier component `C` through
`x₀` is the range of a continuous `1`-periodic curve, injective on `[0,1)`. -/
theorem exists_periodic_param_aux (hVcl : IsCompact (closure V))
    (hfY : SurfaceHarmonicOn f Y) (hx₀fr : x₀ ∈ frontier V) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ 1 ∧
      Set.range γ = connectedComponentIn (frontier V) x₀ ∧
      Set.InjOn γ (Set.Ico (0:ℝ) 1) := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  have hx₀C : x₀ ∈ C := mem_connectedComponentIn hx₀fr
  have hx₀Y : x₀ ∈ Y := hCY hx₀C
  obtain ⟨q₀, hq₀proj⟩ := ConjEtale.exists_mk hfY hYo hx₀Y
  have hq₀C : ConjEtale.proj q₀ ∈ C := by rw [hq₀proj]; exact hx₀C
  set Ê := connectedComponentIn (ConjEtale.proj ⁻¹' C) q₀ with hÊ
  have hq₀Ê : q₀ ∈ Ê := mem_connectedComponentIn hq₀C
  have hÊsub : Ê ⊆ ConjEtale.proj ⁻¹' C := connectedComponentIn_subset _ _
  obtain ⟨E, hEcont, hevE, hEmem, hEinv, hInj⟩ :=
    exists_evIm_inverse hVo hdich hfc hchart hYo hCY hVcl hq₀C
  -- deck-group closure properties
  have hshiftÊ : ∀ r : ℝ, shift r q₀ ∈ Ê → shift r '' Ê = Ê := by
    intro r hr
    have h1 : shift r '' Ê = connectedComponentIn (ConjEtale.proj ⁻¹' C) (shift r q₀) :=
      shift_image_component r hq₀C
    rw [h1, hÊ]
    exact (connectedComponentIn_eq hr).symm
  have hGzero : shift 0 q₀ ∈ Ê := by rw [shift_zero]; exact hq₀Ê
  have hGadd : ∀ r s : ℝ, shift r q₀ ∈ Ê → shift s q₀ ∈ Ê → shift (r + s) q₀ ∈ Ê := by
    intro r s hr hs
    have h1 : shift (r + s) q₀ = shift r (shift s q₀) := (shift_shift r s q₀).symm
    rw [h1, ← hshiftÊ r hr]
    exact ⟨shift s q₀, hs, rfl⟩
  have hGneg : ∀ r : ℝ, shift r q₀ ∈ Ê → shift (-r) q₀ ∈ Ê := by
    intro r hr
    have h1 : shift (-r) '' Ê = connectedComponentIn (ConjEtale.proj ⁻¹' C) (shift (-r) q₀) :=
      shift_image_component (-r) hq₀C
    have h2 : q₀ ∈ shift (-r) '' Ê := ⟨shift r q₀, hr, shift_neg_shift r q₀⟩
    rw [h1] at h2
    have h3 := connectedComponentIn_eq h2
    have h4 : ConjEtale.proj (shift (-r) q₀) ∈ C := by rw [proj_shift]; exact hq₀C
    have h5 : shift (-r) q₀ ∈ connectedComponentIn (ConjEtale.proj ⁻¹' C) (shift (-r) q₀) :=
      mem_connectedComponentIn h4
    rw [h3] at h5
    exact h5
  set G : AddSubgroup ℝ :=
    { carrier := {r : ℝ | shift r q₀ ∈ Ê},
      zero_mem' := hGzero,
      add_mem' := fun {a b} ha hb => hGadd a b ha hb,
      neg_mem' := fun {a} ha => hGneg a ha } with hGdef
  have hmemG : ∀ r : ℝ, r ∈ G ↔ shift r q₀ ∈ Ê := fun r => Iff.rfl
  -- fibre transitivity into the deck group
  have hfibG : ∀ q ∈ Ê, ∀ q' ∈ Ê, ConjEtale.proj q = ConjEtale.proj q' →
      evIm q' - evIm q ∈ G := by
    intro q hq q' hq' hproj
    have h1 : q' = shift (evIm q' - evIm q) q := shift_eq_of_proj_eq hproj
    have hqC' : ConjEtale.proj q ∈ C :=
      Set.mem_preimage.mp (hÊsub hq)
    have h2 : shift (evIm q' - evIm q) '' connectedComponentIn (ConjEtale.proj ⁻¹' C) q
        = connectedComponentIn (ConjEtale.proj ⁻¹' C) (shift (evIm q' - evIm q) q) :=
      shift_image_component _ hqC'
    have hcompq : connectedComponentIn (ConjEtale.proj ⁻¹' C) q = Ê := by
      rw [hÊ]; exact (connectedComponentIn_eq hq).symm
    have hcompq' : connectedComponentIn (ConjEtale.proj ⁻¹' C)
        (shift (evIm q' - evIm q) q) = Ê := by
      rw [← h1, hÊ]; exact (connectedComponentIn_eq hq').symm
    rw [hcompq, hcompq'] at h2
    show shift (evIm q' - evIm q) q₀ ∈ Ê
    rw [← h2]
    exact ⟨q₀, hq₀Ê, rfl⟩
  -- deck-equivariance of the global section
  have hEshift : ∀ r ∈ G, ∀ t : ℝ, E (t + r) = shift r (E t) := by
    intro r hr t
    have h1 : shift r (E t) ∈ Ê := by
      rw [← hshiftÊ r hr]
      exact ⟨E t, hEmem t, rfl⟩
    refine hInj (hEmem (t + r)) h1 ?_
    rw [hevE, evIm_shift, hevE]
  -- the projected curve
  set γ₀ : ℝ → X := fun t => ConjEtale.proj (E t) with hγ₀def
  have hγ₀cont : Continuous γ₀ := ConjEtale.continuous_proj.comp hEcont
  have hγ₀C : ∀ t, γ₀ t ∈ C := fun t => Set.mem_preimage.mp (hÊsub (hEmem t))
  have hprojÊ : ConjEtale.proj '' Ê = C :=
    proj_image_component_eq hVo hdich hfc hchart hYo hCY hfY hq₀C
  have hrangeC : Set.range γ₀ = C := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩; exact hγ₀C t
    · intro y hy
      obtain ⟨p, hpÊ, hpy⟩ : y ∈ ConjEtale.proj '' Ê := hprojÊ ▸ hy
      refine ⟨evIm p, ?_⟩
      show ConjEtale.proj (E (evIm p)) = y
      rw [hEinv p hpÊ]
      exact hpy
  -- G is nontrivial
  have hGne : ∃ r ∈ G, r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hprojinj : Set.InjOn ConjEtale.proj Ê := by
      intro p hp p' hp' hproj
      have hr := hfibG p hp p' hp' hproj
      have h0 : evIm p' - evIm p = 0 := hcon _ hr
      have : evIm p = evIm p' := by linarith
      exact hInj hp hp' this
    have hγ₀inj : Function.Injective γ₀ := by
      intro t t' h
      have h1 : E t = E t' := hprojinj (hEmem t) (hEmem t') h
      have h2 := congrArg evIm h1
      rwa [hevE, hevE] at h2
    -- finite cover of `C` by arc neighbourhoods traced by `γ₀`
    have hexists : ∀ y ∈ C, ∃ (t r : ℝ) (U : Set X), 0 < r ∧ IsOpen U ∧ y ∈ U ∧
        ∀ y' ∈ C ∩ U, ∃ s : ℝ, |s - t| < r ∧ γ₀ s = y' := by
      intro y hy
      obtain ⟨p, hpÊ, hpy⟩ : y ∈ ConjEtale.proj '' Ê := hprojÊ ▸ hy
      have hpC : ConjEtale.proj p ∈ C := Set.mem_preimage.mp (hÊsub hpÊ)
      obtain ⟨r, U, hr, hUo, hpU, hcov⟩ :=
        exists_proj_arc_nbhd hVo hdich hfc hchart hYo hCY hpC
      refine ⟨evIm p, r, U, hr, hUo, by rw [← hpy]; exact hpU, ?_⟩
      intro y' hy'
      obtain ⟨w, hw, hwproj, hwbd⟩ := hcov y' hy'
      have hwÊ : w ∈ Ê := by
        have hcomp : connectedComponentIn (ConjEtale.proj ⁻¹' C) p = Ê := by
          rw [hÊ]; exact (connectedComponentIn_eq hpÊ).symm
        rw [← hcomp]; exact hw
      refine ⟨evIm w, hwbd, ?_⟩
      show ConjEtale.proj (E (evIm w)) = y'
      rw [hEinv w hwÊ]; exact hwproj
    choose! tf rf Uf hrf hUfo hyUf hUfcov using hexists
    have hcovC : C ⊆ ⋃ y ∈ C, Uf y := fun y hy => Set.mem_biUnion hy (hyUf y hy)
    obtain ⟨T, hTsub, hTfin, hTcov⟩ :=
      (isCompact_component hVcl (x₀ := x₀)).elim_finite_subcover_image
        (fun y hy => hUfo y hy) hcovC
    have hTne : T.Nonempty := by
      obtain ⟨y₁, hy₁T, -⟩ := Set.mem_iUnion₂.mp (hTcov hx₀C)
      exact ⟨y₁, hy₁T⟩
    have hTfne : hTfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hTfin).mpr hTne
    set M := hTfin.toFinset.sup' hTfne (fun y => |tf y| + rf y) with hM
    have hbound : ∀ y' ∈ C, ∃ s : ℝ, |s| ≤ M ∧ γ₀ s = y' := by
      intro y' hy'
      obtain ⟨y, hyT, hy'U⟩ := Set.mem_iUnion₂.mp (hTcov hy')
      obtain ⟨s, hsbd, hsy⟩ := hUfcov y (hTsub hyT) y' ⟨hy', hy'U⟩
      refine ⟨s, ?_, hsy⟩
      have h1 : |tf y| + rf y ≤ M :=
        Finset.le_sup' (fun y => |tf y| + rf y) (hTfin.mem_toFinset.mpr hyT)
      have h2 : |s| ≤ |tf y| + |s - tf y| := by
        calc |s| = |tf y + (s - tf y)| := by congr 1; ring
          _ ≤ |tf y| + |s - tf y| := abs_add_le _ _
      linarith
    have hMpos : 0 < M := by
      obtain ⟨y₁, hy₁T⟩ := hTne
      have h1 : |tf y₁| + rf y₁ ≤ M :=
        Finset.le_sup' (fun y => |tf y| + rf y) (hTfin.mem_toFinset.mpr hy₁T)
      have h2 : 0 < rf y₁ := hrf y₁ (hTsub hy₁T)
      have h3 : 0 ≤ |tf y₁| := abs_nonneg _
      linarith
    obtain ⟨s, hsM, hs⟩ := hbound (γ₀ (M + 1)) (hγ₀C (M + 1))
    have hseq : s = M + 1 := hγ₀inj hs
    rw [hseq] at hsM
    have : |M + 1| = M + 1 := abs_of_pos (by linarith)
    linarith [this ▸ hsM]
  -- G is not dense
  have hnotdense : ¬ Dense (G : Set ℝ) := by
    intro hdense
    have hclosed : IsClosed {t' : ℝ | γ₀ t' = γ₀ 0} := isClosed_eq hγ₀cont continuous_const
    have hsubset : (G : Set ℝ) ⊆ {t' : ℝ | γ₀ t' = γ₀ 0} := by
      intro rr hrr
      show γ₀ rr = γ₀ 0
      show ConjEtale.proj (E rr) = ConjEtale.proj (E 0)
      have h1 : E rr = E (0 + rr) := by norm_num
      rw [h1, hEshift rr hrr 0, proj_shift]
    have hconst : ∀ t' : ℝ, γ₀ t' = γ₀ 0 := by
      intro t'
      have h1 : t' ∈ closure (G : Set ℝ) := hdense t'
      exact closure_minimal hsubset hclosed h1
    -- but C contains two distinct points (a local boundary arc)
    obtain ⟨W', a, b, arc, linv, hW'o, hx₀W', hab, harcx₀, hcarc, hclinv,
      harcmem, hlinvarc, harclinv, hlinvmem, himg, hpre, hx₀sl, hslsub⟩ :=
      exists_local_arc_in_component hVo hdich hfc hchart (mem_connectedComponentIn hx₀fr)
    set s₁ := a + (b - a) / 3 with hs₁
    set s₂ := a + 2 * (b - a) / 3 with hs₂
    have hs₁m : s₁ ∈ Set.Ioo a b := ⟨by rw [hs₁]; linarith, by rw [hs₁]; linarith⟩
    have hs₂m : s₂ ∈ Set.Ioo a b := ⟨by rw [hs₂]; linarith, by rw [hs₂]; linarith⟩
    have hne12 : arc s₁ ≠ arc s₂ := by
      intro hcontra
      have h1 : s₁ = s₂ := by
        rw [← hlinvarc s₁ hs₁m, ← hlinvarc s₂ hs₂m, hcontra]
      rw [hs₁, hs₂] at h1
      have : b - a > 0 := by linarith
      linarith
    have h₁C : arc s₁ ∈ C := hslsub (harcmem s₁ hs₁m)
    have h₂C : arc s₂ ∈ C := hslsub (harcmem s₂ hs₂m)
    -- C = range γ₀ is a singleton, contradiction
    obtain ⟨u₁, hu₁⟩ : arc s₁ ∈ Set.range γ₀ := hrangeC ▸ h₁C
    obtain ⟨u₂, hu₂⟩ : arc s₂ ∈ Set.range γ₀ := hrangeC ▸ h₂C
    apply hne12
    rw [← hu₁, ← hu₂, hconst u₁, hconst u₂]
  -- G is cyclic with positive generator t₀
  obtain ⟨g, hGg⟩ := (AddSubgroup.dense_or_cyclic G).resolve_left hnotdense
  have hgne : g ≠ 0 := by
    rintro rfl
    obtain ⟨r, hrG, hrne⟩ := hGne
    have hbot : G = ⊥ := by
      rw [hGg]
      refine le_antisymm ((AddSubgroup.closure_le ⊥).mpr ?_) bot_le
      simp
    rw [hbot, AddSubgroup.mem_bot] at hrG
    exact hrne hrG
  set t₀ := |g| with ht₀
  have ht₀pos : 0 < t₀ := abs_pos.mpr hgne
  have hgG : g ∈ G := by rw [hGg]; exact AddSubgroup.subset_closure rfl
  have ht₀G : t₀ ∈ G := by
    rcases abs_choice g with h | h
    · rw [ht₀, h]; exact hgG
    · rw [ht₀, h]; exact neg_mem hgG
  have hmemt₀ : ∀ r ∈ G, ∃ n : ℤ, r = n * t₀ := by
    intro r hrG
    rw [hGg] at hrG
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hrG
    rcases abs_choice g with h | h
    · exact ⟨n, by rw [← hn, zsmul_eq_mul, ht₀, h]⟩
    · refine ⟨-n, ?_⟩
      rw [← hn, zsmul_eq_mul, ht₀, h]
      push_cast
      ring
  -- periodicity of γ₀
  have hper₀ : ∀ t, γ₀ (t + t₀) = γ₀ t := by
    intro t
    show ConjEtale.proj (E (t + t₀)) = ConjEtale.proj (E t)
    rw [hEshift t₀ ht₀G t, proj_shift]
  -- injectivity of γ₀ on a fundamental domain
  have hinj₀ : Set.InjOn γ₀ (Set.Ico 0 t₀) := by
    intro s hs s' hs' hss
    have h1 : evIm (E s') - evIm (E s) ∈ G := hfibG (E s) (hEmem s) (E s') (hEmem s') hss
    rw [hevE, hevE] at h1
    obtain ⟨n, hn⟩ := hmemt₀ _ h1
    have hb : |s' - s| < t₀ := by
      rw [abs_lt]
      exact ⟨by linarith [hs.2, hs'.1], by linarith [hs'.2, hs.1]⟩
    rw [hn, abs_mul, abs_of_pos ht₀pos] at hb
    have hn1 : |(n : ℝ)| < 1 := by
      by_contra hcontra
      push Not at hcontra
      nlinarith
    have hn0 : n = 0 := by
      by_contra hcontra
      have h2 : (1 : ℤ) ≤ |n| := Int.one_le_abs hcontra
      have h2' : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.mpr h2
      rw [Int.cast_abs, Int.cast_one] at h2'
      linarith
    have h4 : s' - s = 0 := by rw [hn, hn0]; push_cast; ring
    linarith
  -- rescale to period 1
  refine ⟨fun t => γ₀ (t₀ * t), hγ₀cont.comp (continuous_const.mul continuous_id), ?_, ?_, ?_⟩
  · intro t
    show γ₀ (t₀ * (t + 1)) = γ₀ (t₀ * t)
    have h1 : t₀ * (t + 1) = t₀ * t + t₀ := by ring
    rw [h1, hper₀]
  · rw [← hrangeC]
    apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩; exact ⟨t₀ * t, rfl⟩
    · rintro _ ⟨t, rfl⟩
      refine ⟨t / t₀, ?_⟩
      show γ₀ (t₀ * (t / t₀)) = γ₀ t
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt ht₀pos)]
  · intro s hs s' hs' hss
    have h1 : t₀ * s ∈ Set.Ico 0 t₀ := by
      constructor
      · exact mul_nonneg (le_of_lt ht₀pos) hs.1
      · calc t₀ * s < t₀ * 1 := by
              exact mul_lt_mul_of_pos_left hs.2 ht₀pos
          _ = t₀ := mul_one t₀
    have h2 : t₀ * s' ∈ Set.Ico 0 t₀ := by
      constructor
      · exact mul_nonneg (le_of_lt ht₀pos) hs'.1
      · calc t₀ * s' < t₀ * 1 := mul_lt_mul_of_pos_left hs'.2 ht₀pos
          _ = t₀ := mul_one t₀
    have h3 : t₀ * s = t₀ * s' := hinj₀ h1 h2 hss
    exact mul_left_cancel₀ (ne_of_gt ht₀pos) h3

end LocalInj

/-! ## The frozen W7 target -/

/-- **Periodic parametrisation of a frontier component (W7).**  Under the collar
hypotheses — `V` open with compact closure, `f` harmonic on an open `A ⊇ ∂V`,
the dichotomy `hdich`, the level condition `hfc`, and the straightening germ
payload `hchart` — the connected component of `frontier V` through `x₀` is a
topological circle: the range of a continuous `1`-periodic curve `γ : ℝ → X`
injective on the fundamental domain `[0,1)`. -/
theorem exists_periodic_param [T2Space X] {V : Set X} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {A : Set X} (hharm : Rado.SurfaceHarmonicOn f A) (hAo : IsOpen A) (hfrA : frontier V ⊆ A)
    {x₀ : X} (hx₀ : x₀ ∈ frontier V) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ 1 ∧
      Set.range γ = connectedComponentIn (frontier V) x₀ ∧
      Set.InjOn γ (Set.Ico (0:ℝ) 1) := by
  obtain ⟨Y, hYo, hYc, hx₀Y, hfY, hCY, -⟩ :=
    exists_collar_component hdich hharm hAo hfrA hx₀
  exact exists_periodic_param_aux hVo hdich hfc hchart hYo hCY hVcl hfY hx₀


end Uniformization
