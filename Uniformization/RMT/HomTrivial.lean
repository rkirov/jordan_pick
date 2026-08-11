/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Hom-trivial variants of the branch machinery and RMT

The ported Riemann-mapping layer (`Uniformization/RMT/RiemannMapping.lean`) proves the existence of
holomorphic branches of `log` and `n`-th roots, and ultimately the Riemann mapping theorem, under the
hypothesis `IsSimplyConnected U`.  For the uniformization theorem with the weaker `H¹(X, ℝ) = 0`
hypothesis (`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)`, see `Uniformization/Main.lean`)
we need the same conclusions under a *hom-trivial* hypothesis on the loops of `U`.

`IsSimplyConnected U` is used in those proofs *only* to lift a continuous map `U → ℂ∗` through the
exponential covering `exp : ℂ → ℂ∗`.  The general lifting criterion
(`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`) only needs `f⁎ π₁(U) ⊆ p⁎ π₁(ℂ)`,
and since `ℂ` is simply connected the target is trivial, so it suffices that `f⁎ π₁(U)` is trivial.
We detect this with the *winding number homomorphism*
`windingHom : Additive (FundamentalGroup ℂ∗ b) →+ ℝ`: composing with `f⁎` gives an element of
`Additive (FundamentalGroup U) →+ ℝ`, which the hom-trivial hypothesis forces to be zero, and a
zero winding number is exactly a closed lift, i.e. membership in `p⁎ π₁(ℂ)`.
-/

open Set Topology unitInterval Function
open scoped Real

namespace Complex

/-! ### The exponential covering `ℂ → ℂ∖{0}` -/

/-- The exponential regarded as a map to the punctured plane `ℂ∖{0}`; this is a covering map with
contractible total space `ℂ`. -/
noncomputable def expCovMap (z : ℂ) : {z : ℂ // z ≠ 0} := ⟨Complex.exp z, z.exp_ne_zero⟩

@[simp] theorem expCovMap_coe (z : ℂ) : (expCovMap z : ℂ) = Complex.exp z := rfl

theorem isCoveringMap_expCovMap : IsCoveringMap expCovMap := isCoveringMap_exp

/-- Translating the argument by `w` with `exp w = 1` does not change `expCovMap`. -/
theorem expCovMap_add_right {w : ℂ} (hw : Complex.exp w = 1) (z : ℂ) :
    expCovMap (z + w) = expCovMap z :=
  Subtype.ext <| by simp [expCovMap, Complex.exp_add, hw]

/-! ### The winding-number machinery for `expCovMap` -/

/-- Shifting the starting point of a lifted path (through `expCovMap`) by `w` with `exp w = 1`
shifts the endpoint by `w`. -/
theorem liftPath_apply_one_of_exp_eq (γ : C(I, {z : ℂ // z ≠ 0})) (e e' : ℂ)
    (h : γ 0 = expCovMap e) (h' : γ 0 = expCovMap e') (hexp : Complex.exp e' = Complex.exp e) :
    isCoveringMap_expCovMap.liftPath γ e' h' 1
      = isCoveringMap_expCovMap.liftPath γ e h 1 + (e' - e) := by
  set cov := isCoveringMap_expCovMap
  set Γ := cov.liftPath γ e h with hΓ
  have hw : Complex.exp (e' - e) = 1 := by
    rw [Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero e)]
  have hΓ2 : (⟨fun t ↦ Γ t + (e' - e), by fun_prop⟩ : C(I, ℂ)) = cov.liftPath γ e' h' := by
    rw [cov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · refine funext fun t ↦ ?_
      show expCovMap (Γ t + (e' - e)) = γ t
      rw [expCovMap_add_right hw]
      exact congr_fun (cov.liftPath_lifts γ e h) t
    · show Γ 0 + (e' - e) = e'
      rw [show Γ 0 = e from cov.liftPath_zero γ e h]; ring
  have := DFunLike.congr_fun hΓ2 1
  simp only [ContinuousMap.coe_mk] at this
  rw [← this]

/-- The endpoint of the lift of (a representative of) `ζ` starting at `e₀`. -/
private noncomputable def windEnd (b : {z : ℂ // z ≠ 0}) (e₀ : ℂ) (he : expCovMap e₀ = b)
    (ζ : FundamentalGroup {z : ℂ // z ≠ 0} b) : ℂ :=
  (isCoveringMap_expCovMap.monodromy (FundamentalGroup.toPath ζ) ⟨e₀, he⟩).1

variable {b : {z : ℂ // z ≠ 0}} {e₀ : ℂ} (he : expCovMap e₀ = b)

theorem expCovMap_windEnd (ζ : FundamentalGroup {z : ℂ // z ≠ 0} b) :
    expCovMap (windEnd b e₀ he ζ) = b :=
  (isCoveringMap_expCovMap.monodromy (FundamentalGroup.toPath ζ) ⟨e₀, he⟩).2

/-- Translation independence of the lift endpoint, at the level of the monodromy action. -/
theorem monodromy_val_sub (ζ : Path.Homotopic.Quotient b b) (e e' : ℂ)
    (he : expCovMap e = b) (he' : expCovMap e' = b) :
    (isCoveringMap_expCovMap.monodromy ζ ⟨e', he'⟩).1 - e'
      = (isCoveringMap_expCovMap.monodromy ζ ⟨e, he⟩).1 - e := by
  induction ζ using Quotient.ind with
  | _ γ =>
    have hexp : Complex.exp e' = Complex.exp e := by
      have h2 : expCovMap e' = expCovMap e := by rw [he, he']
      simpa [expCovMap] using congr_arg Subtype.val h2
    have hstart : (γ : C(I, {z : ℂ // z ≠ 0})) 0 = expCovMap e := by
      show γ 0 = expCovMap e; rw [γ.source, he]
    have hstart' : (γ : C(I, {z : ℂ // z ≠ 0})) 0 = expCovMap e' := by
      show γ 0 = expCovMap e'; rw [γ.source, he']
    show isCoveringMap_expCovMap.liftPath _ e' _ 1 - e'
        = isCoveringMap_expCovMap.liftPath _ e _ 1 - e
    rw [liftPath_apply_one_of_exp_eq (γ : C(I, {z : ℂ // z ≠ 0})) e e' hstart hstart' hexp]
    ring

theorem windEnd_one : windEnd b e₀ he 1 = e₀ := by
  have h1 : FundamentalGroup.toPath (1 : FundamentalGroup {z : ℂ // z ≠ 0} b)
      = Path.Homotopic.Quotient.refl b := rfl
  unfold windEnd
  rw [h1, isCoveringMap_expCovMap.monodromy_refl]
  rfl

/-- The endpoint of the lift starting at any point `e` in the fibre over `b`. -/
theorem monodromy_val_at (ζ : FundamentalGroup {z : ℂ // z ≠ 0} b) (e : ℂ)
    (hemem : expCovMap e = b) :
    (isCoveringMap_expCovMap.monodromy (FundamentalGroup.toPath ζ) ⟨e, hemem⟩).1
      = e + (windEnd b e₀ he ζ - e₀) := by
  have h := monodromy_val_sub (FundamentalGroup.toPath ζ) e₀ e he hemem
  have hd : windEnd b e₀ he ζ
      = (isCoveringMap_expCovMap.monodromy (FundamentalGroup.toPath ζ) ⟨e₀, he⟩).1 := rfl
  rw [hd]; linear_combination h

theorem windEnd_mul (ζ θ : FundamentalGroup {z : ℂ // z ≠ 0} b) :
    windEnd b e₀ he (ζ * θ) = windEnd b e₀ he θ + windEnd b e₀ he ζ - e₀ := by
  have hmul : FundamentalGroup.toPath (ζ * θ)
      = (FundamentalGroup.toPath θ).trans (FundamentalGroup.toPath ζ) := rfl
  have hθmem : expCovMap (windEnd b e₀ he θ) = b := expCovMap_windEnd he θ
  have hstep : windEnd b e₀ he (ζ * θ)
      = (isCoveringMap_expCovMap.monodromy (FundamentalGroup.toPath ζ)
          (isCoveringMap_expCovMap.monodromy (FundamentalGroup.toPath θ) ⟨e₀, he⟩)).1 := by
    unfold windEnd; rw [hmul, isCoveringMap_expCovMap.monodromy_trans_apply]
  rw [hstep]
  have hinner : isCoveringMap_expCovMap.monodromy (FundamentalGroup.toPath θ) ⟨e₀, he⟩
      = ⟨windEnd b e₀ he θ, hθmem⟩ := rfl
  rw [hinner, monodromy_val_at he ζ (windEnd b e₀ he θ) hθmem]
  ring

/-- The winding-number homomorphism on `π₁(ℂ∖{0}, b)`, valued in `ℝ`.  It sends the class of a loop
to `1/(2π)` times the imaginary part of the gap between the endpoints of a lift through `expCovMap`.
It vanishes exactly on classes whose lift is closed, i.e. on `p⁎ π₁(ℂ)`. -/
noncomputable def windingHom (b : {z : ℂ // z ≠ 0}) (e₀ : ℂ) (he : expCovMap e₀ = b) :
    Additive (FundamentalGroup {z : ℂ // z ≠ 0} b) →+ ℝ where
  toFun ξ := ((windEnd b e₀ he (Additive.toMul ξ)) - e₀).im / (2 * π)
  map_zero' := by
    show ((windEnd b e₀ he 1) - e₀).im / (2 * π) = 0
    rw [windEnd_one he]; simp
  map_add' ξ η := by
    show ((windEnd b e₀ he (Additive.toMul ξ * Additive.toMul η)) - e₀).im / (2 * π)
        = ((windEnd b e₀ he (Additive.toMul ξ)) - e₀).im / (2 * π)
          + ((windEnd b e₀ he (Additive.toMul η)) - e₀).im / (2 * π)
    rw [windEnd_mul he]
    have hrw : (windEnd b e₀ he (Additive.toMul η) + windEnd b e₀ he (Additive.toMul ξ) - e₀ - e₀)
        = (windEnd b e₀ he (Additive.toMul ξ) - e₀)
          + (windEnd b e₀ he (Additive.toMul η) - e₀) := by ring
    rw [hrw, Complex.add_im, add_div]

@[simp] theorem windingHom_apply (ξ : Additive (FundamentalGroup {z : ℂ // z ≠ 0} b)) :
    windingHom b e₀ he ξ = ((windEnd b e₀ he (Additive.toMul ξ)) - e₀).im / (2 * π) := rfl

/-- If the winding number of `ζ` vanishes then `ζ` lies in the image of `π₁(ℂ)` under the covering,
which is the range condition needed by the general lifting criterion. -/
theorem mem_range_mapOfEq_of_windingHom_eq_zero
    (ζ : FundamentalGroup {z : ℂ // z ≠ 0} b)
    (h : windingHom b e₀ he (Additive.ofMul ζ) = 0) :
    ζ ∈ (FundamentalGroup.mapOfEq ⟨expCovMap, isCoveringMap_expCovMap.continuous⟩ he).range := by
  set cov := isCoveringMap_expCovMap
  induction ζ using Quotient.ind with
  | _ γ =>
    -- extract vanishing of the imaginary part of the gap
    have hpi : (2 * π) ≠ 0 := by positivity
    rw [windingHom_apply, toMul_ofMul, div_eq_zero_iff, or_iff_left hpi] at h
    -- the gap has `exp = 1`, hence both its real and imaginary parts vanish
    have hexp1 : Complex.exp (windEnd b e₀ he ⟦γ⟧ - e₀) = 1 := by
      rw [Complex.exp_sub]
      have h2 : expCovMap (windEnd b e₀ he ⟦γ⟧) = expCovMap e₀ := by
        rw [expCovMap_windEnd he, he]
      have h3 := congr_arg Subtype.val h2
      simp only [expCovMap_coe] at h3
      rw [h3, div_self (Complex.exp_ne_zero e₀)]
    have hend : windEnd b e₀ he ⟦γ⟧ = e₀ := by
      have hre : (windEnd b e₀ he ⟦γ⟧ - e₀).re = 0 := by
        have hnorm : ‖Complex.exp (windEnd b e₀ he ⟦γ⟧ - e₀)‖ = 1 := by rw [hexp1]; simp
        rw [Complex.norm_exp] at hnorm
        exact (Real.exp_eq_one_iff _).1 hnorm
      have hz : windEnd b e₀ he ⟦γ⟧ - e₀ = 0 := Complex.ext hre h
      linear_combination hz
    -- the lift of `γ` from `e₀` is a loop in `ℂ`
    have hΓend : cov.liftPath (γ : C(I, {z : ℂ // z ≠ 0})) e₀
        (by show γ 0 = expCovMap e₀; rw [γ.source, he]) 1 = e₀ := hend
    set Γ := cov.liftPath (γ : C(I, {z : ℂ // z ≠ 0})) e₀
        (by show γ 0 = expCovMap e₀; rw [γ.source, he]) with hΓdef
    have hΓ0 : Γ 0 = e₀ := cov.liftPath_zero _ _ _
    have hlift : ∀ t, expCovMap (Γ t) = γ t := fun t ↦
      congr_fun (cov.liftPath_lifts (γ : C(I, {z : ℂ // z ≠ 0})) e₀
        (by show γ 0 = expCovMap e₀; rw [γ.source, he])) t
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ⟨Γ, hΓ0, hΓend⟩), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply]
    have hpaths :
        (Path.map (⟨Γ, hΓ0, hΓend⟩ : Path e₀ e₀)
          (ContinuousMap.continuous ⟨expCovMap, cov.continuous⟩)).cast he.symm he.symm = γ := by
      ext t
      exact congr_arg Subtype.val (hlift t)
    rw [hpaths]
    rfl

end Complex

/-! ### Hom-trivial loops -/

/-- `U` has *hom-trivial loops* if every additive `ℝ`-valued homomorphism out of the fundamental
group of `U` (at any basepoint) is zero.  For a connected `U` this is `H¹(U, ℝ) = 0` and matches the
hypothesis of `LeanEval.Geometry.uniformization`. -/
def HomTrivialLoops {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  ∀ (x : X) (hx : x ∈ U), Subsingleton (Additive (FundamentalGroup U ⟨x, hx⟩) →+ ℝ)

/-- Space-level version of `HomTrivialLoops`: every additive `ℝ`-valued homomorphism out of the
fundamental group (at any basepoint) is zero. -/
def HomTrivialSpace (A : Type*) [TopologicalSpace A] : Prop :=
  ∀ a : A, Subsingleton (Additive (FundamentalGroup A a) →+ ℝ)

theorem homTrivialLoops_iff_homTrivialSpace {X : Type*} [TopologicalSpace X] (U : Set X) :
    HomTrivialLoops U ↔ HomTrivialSpace ↥U :=
  ⟨fun h x ↦ h x.1 x.2, fun h x hx ↦ h ⟨x, hx⟩⟩

namespace Complex

/-- Branch of the logarithm on a set with hom-trivial loops (weakening `IsSimplyConnected` in
`Complex.exists_branch_log` to `HomTrivialLoops` + connectivity). -/
theorem exists_branch_log_of_homTrivial {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    {U : Set X} (hUt : HomTrivialLoops U) (hUconn : IsConnected U) (hUo : IsOpen U)
    {g : X → ℂ} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ EqOn (Complex.exp ∘ f) g U := by
  classical
  haveI hlpc : LocallyPathConnectedSpace ↥U := hUo.locallyPathConnectedSpace
  haveI hconn : ConnectedSpace ↥U := Subtype.connectedSpace hUconn
  haveI hpc : PathConnectedSpace ↥U := pathConnectedSpace_iff_connectedSpace.mpr hconn
  obtain ⟨x₀, hx₀U⟩ := hUconn.nonempty
  have hgne : ∀ x : ↥U, g ↑x ≠ 0 := fun x ↦ ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀
  have hx₀ : g x₀ ≠ 0 := hgne ⟨x₀, hx₀U⟩
  set a₀ : ↥U := ⟨x₀, hx₀U⟩ with ha₀
  set fC : C(↥U, {z : ℂ // z ≠ 0}) :=
    ⟨fun x ↦ ⟨g ↑x, hgne x⟩, (continuousOn_iff_continuous_domRestrict.mp hgc).subtype_mk hgne⟩ with hfC
  set e₀ : ℂ := Complex.log (g x₀) with he₀
  have he : expCovMap e₀ = fC a₀ := Subtype.ext (Complex.exp_log hx₀)
  -- the range condition, via the hom-trivial hypothesis and the winding homomorphism
  have hrange : (FundamentalGroup.map fC a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨expCovMap, isCoveringMap_expCovMap.continuous⟩ he).range := by
    rintro _ ⟨η, rfl⟩
    haveI := hUt x₀ hx₀U
    have hW : (windingHom (fC a₀) e₀ he).comp ((FundamentalGroup.map fC a₀).toAdditive)
        = 0 := Subsingleton.elim _ _
    have hval : windingHom (fC a₀) e₀ he (Additive.ofMul (FundamentalGroup.map fC a₀ η)) = 0 := by
      have := DFunLike.congr_fun hW (Additive.ofMul η)
      simpa [MonoidHom.coe_toAdditive] using this
    exact mem_range_mapOfEq_of_windingHom_eq_zero he _ hval
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    isCoveringMap_expCovMap.existsUnique_continuousMap_lifts_of_range_le he hrange
  have hFg : ∀ x : ↥U, Complex.exp (F x) = g ↑x := fun x ↦ by
    have := congr_fun hF x
    simpa [expCovMap, hfC] using congr_arg Subtype.val this
  obtain ⟨f, hf⟩ : ∃ f : X → ℂ, ∀ z : ↥U, f ↑z = F z :=
    ⟨fun z ↦ if hz : z ∈ U then F ⟨z, hz⟩ else 0, by intro z; simp⟩
  refine ⟨f, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert map_continuous F using 1
    ext z; exact hf z
  · intro x hx
    have hfx : f x = F ⟨x, hx⟩ := hf ⟨x, hx⟩
    simp only [Function.comp_apply, hfx]
    exact hFg ⟨x, hx⟩

/-- Branch of an `n`-th root on a set with hom-trivial loops. -/
theorem exists_branch_nthRoot_of_homTrivial {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {U : Set X} (hUt : HomTrivialLoops U) (hUconn : IsConnected U)
    (hUo : IsOpen U) {g : X → ℂ} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) {n : ℕ} (hn : n ≠ 0) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  classical
  rcases exists_branch_log_of_homTrivial hUt hUconn hUo hgc hU₀ with ⟨f, hfc, hf⟩
  refine ⟨U.piecewise (Complex.exp <| f · / n) (g · ^ (1 / n : ℂ)), ?_, fun z ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, restrict_piecewise,
      ← continuousOn_iff_continuous_domRestrict]
    fun_prop
  · by_cases hz : z ∈ U
    · simp [hz, ← Complex.exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), ← hf hz,
        Function.comp_apply]
    · simp [hz, ← Complex.cpow_mul_nat, hn]

end Complex

/-! ### Transfer lemmas -/

/-- A simply connected space has hom-trivial loops (the fundamental group is trivial). -/
theorem homTrivialSpace_of_simplyConnected {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] : HomTrivialSpace A := by
  intro a
  haveI : Subsingleton (Additive (FundamentalGroup A a)) :=
    inferInstanceAs (Subsingleton (FundamentalGroup A a))
  exact ⟨fun f g ↦ AddMonoidHom.ext fun α ↦ by
    rw [Subsingleton.elim α 0, map_zero, map_zero]⟩

/-- Hom-triviality passes from `X` to `A` along a retraction `r : X → A` (`r ∘ ι = id`).
This is the abstract heart of the retract transfer: any additive hom out of `π₁(A)` is the
pullback along `r⁎` of a hom out of `π₁(X)`, which the hom-trivial hypothesis on `X` kills. -/
theorem homTrivialSpace_of_retract {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (ι : C(A, X)) (r : C(X, A)) (hri : ∀ a, r (ι a) = a) (hX : HomTrivialSpace X) :
    HomTrivialSpace A := by
  intro a
  refine ⟨fun f g ↦ AddMonoidHom.ext fun α ↦ ?_⟩
  -- `r⁎ ∘ ι⁎ = id` on `π₁(A, a)`
  have retr : ∀ ξ : FundamentalGroup A a,
      FundamentalGroup.mapOfEq r (hri a) (FundamentalGroup.map ι a ξ) = ξ := by
    intro ξ
    induction ξ using Quotient.ind with
    | _ γ =>
      rw [show FundamentalGroup.map ι a ⟦γ⟧
            = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ.map ι.continuous)) from rfl,
          FundamentalGroup.mapOfEq_apply]
      have hpaths :
          ((γ.map ι.continuous).map r.continuous).cast (hri a).symm (hri a).symm = γ := by
        ext t; exact hri (γ t)
      rw [hpaths]
      rfl
  haveI := hX (ι a)
  have hfg : f.comp (FundamentalGroup.mapOfEq r (hri a)).toAdditive
      = g.comp (FundamentalGroup.mapOfEq r (hri a)).toAdditive := Subsingleton.elim _ _
  have hid : (FundamentalGroup.mapOfEq r (hri a)).toAdditive
      ((FundamentalGroup.map ι a).toAdditive α) = α := by
    simp only [MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul]
    rw [retr]; rfl
  calc f α
      = f ((FundamentalGroup.mapOfEq r (hri a)).toAdditive
          ((FundamentalGroup.map ι a).toAdditive α)) := by rw [hid]
    _ = (f.comp (FundamentalGroup.mapOfEq r (hri a)).toAdditive)
          ((FundamentalGroup.map ι a).toAdditive α) := rfl
    _ = (g.comp (FundamentalGroup.mapOfEq r (hri a)).toAdditive)
          ((FundamentalGroup.map ι a).toAdditive α) := by rw [hfg]
    _ = g ((FundamentalGroup.mapOfEq r (hri a)).toAdditive
          ((FundamentalGroup.map ι a).toAdditive α)) := rfl
    _ = g α := by rw [hid]

/-- Hom-triviality transfers along a homeomorphism. -/
theorem HomTrivialSpace.of_homeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (φ : A ≃ₜ B) (hA : HomTrivialSpace A) : HomTrivialSpace B :=
  homTrivialSpace_of_retract (⟨φ.symm, φ.symm.continuous⟩ : C(B, A))
    (⟨φ, φ.continuous⟩ : C(A, B)) (fun b ↦ φ.apply_symm_apply b) hA

/-- Simply connected sets have hom-trivial loops (so existing `IsSimplyConnected` callers can feed
the new hom-trivial API). -/
theorem homTrivialLoops_of_isSimplyConnected {X : Type*} [TopologicalSpace X] {U : Set X}
    (h : IsSimplyConnected U) : HomTrivialLoops U := by
  haveI : SimplyConnectedSpace ↥U := h
  exact (homTrivialLoops_iff_homTrivialSpace U).mpr homTrivialSpace_of_simplyConnected

/-- Hom-triviality of loops transfers along a homeomorphism of the ambient subspaces. -/
theorem HomTrivialLoops.of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {V : Set Y} (φ : ↥U ≃ₜ ↥V) (h : HomTrivialLoops U) : HomTrivialLoops V :=
  (homTrivialLoops_iff_homTrivialSpace V).mpr
    (((homTrivialLoops_iff_homTrivialSpace U).mp h).of_homeomorph φ)
