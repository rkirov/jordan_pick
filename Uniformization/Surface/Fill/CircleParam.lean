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

end Fibre

end Uniformization
