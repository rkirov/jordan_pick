/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.RMT.HomTrivial
import Uniformization.Surface.Fill.Push

/-!
# Hom-trivial analogs of the simple-connectivity engines (W8/F3)

The harmonic (F3) route needs the three simple-connectivity engines of the `Fill`
namespace, but weakened from `SimplyConnected`/`IsSimplyConnected` to the
homological hypothesis `HomTrivialSpace`/`HomTrivialLoops`
(`Subsingleton (Additive (FundamentalGroup · ·) →+ ℝ)`, i.e. `H¹(·, ℝ) = 0`).

Three engines are delivered:

1. `lift_endpoint_eq_of_homTrivial` — the crossing-parity engine of `Parity.lean`
   (`lift_endpoint_eq_of_simplyConnected`) with `SimplyConnectedSpace X` replaced
   by `HomTrivialSpace X`.  The proof builds the winding-number homomorphism on
   `π₁(Circle)` for the covering `Circle.exp : ℝ → Circle` (mirroring
   `Complex.windingHom` for `expCovMap`), pushes it forward along the phase map
   `τ`, and lets hom-triviality kill it, forcing every lift to close.

2. `homTrivialLoops_of_closure_push` — the open ↔ closed transfer of `Push.lean`
   (`isSimplyConnected_of_closure`), delivering `HomTrivialLoops V` from
   `HomTrivialSpace ↥(closure V)` and the inward-push hypothesis inventory.  The
   proof avoids any homotopy bookkeeping: for a *given* loop `γ` in `V`, the push
   `g` obtained from `exists_push_into` with `L := range γ` fixes `γ` on the nose,
   so the composite `π₁(V) → π₁(closure V) → π₁(V)` fixes `[γ]`; pulling back an
   arbitrary hom along the second map and killing it with the closure hypothesis
   gives the vanishing.

3. `homTrivialLoops_of_retract_closure` — the retract corollary, combining
   `homTrivialSpace_of_retract` (to obtain `HomTrivialSpace ↥(closure V)` from a
   retraction of a hom-trivial `X` onto `closure V`) with engine 2.
-/

open Set Topology Function
open scoped unitInterval

namespace Uniformization

/-! ## Winding machinery for the covering `Circle.exp : ℝ → Circle`

This mirrors the `Complex.windingHom` machinery of `Uniformization/RMT/HomTrivial.lean`
for the covering `expCovMap : ℂ → ℂ∖{0}`, but for `Circle.exp`.  The lift lives in
`ℝ`, so the winding homomorphism is simply the (real) gap between the endpoints of
a lift, which is additive under loop concatenation. -/

namespace CircleLift

/-- Translating the argument by `w` with `Circle.exp w = 1` does not change
`Circle.exp`. -/
theorem exp_add_right {w : ℝ} (hw : Circle.exp w = 1) (z : ℝ) :
    Circle.exp (z + w) = Circle.exp z := by
  rw [Circle.exp_add, hw, mul_one]

/-- Shifting the starting point of a lifted path (through `Circle.exp`) by `w` with
`Circle.exp w = 1` shifts the endpoint by `w`. -/
theorem liftPath_apply_one_of_exp_eq (γ : C(I, Circle)) (e e' : ℝ)
    (h : γ 0 = Circle.exp e) (h' : γ 0 = Circle.exp e') (hexp : Circle.exp e' = Circle.exp e) :
    Circle.isCoveringMap_exp.liftPath γ e' h' 1
      = Circle.isCoveringMap_exp.liftPath γ e h 1 + (e' - e) := by
  set cov := Circle.isCoveringMap_exp
  set Γ := cov.liftPath γ e h with hΓ
  have hw : Circle.exp (e' - e) = 1 := by
    rw [Circle.exp_sub, hexp, div_self']
  have hΓ2 : (⟨fun t ↦ Γ t + (e' - e), by fun_prop⟩ : C(I, ℝ)) = cov.liftPath γ e' h' := by
    rw [cov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · refine funext fun t ↦ ?_
      show Circle.exp (Γ t + (e' - e)) = γ t
      rw [exp_add_right hw]
      exact congr_fun (cov.liftPath_lifts γ e h) t
    · show Γ 0 + (e' - e) = e'
      rw [show Γ 0 = e from cov.liftPath_zero γ e h]; ring
  have := DFunLike.congr_fun hΓ2 1
  simp only [ContinuousMap.coe_mk] at this
  rw [← this]

/-- The endpoint of the lift of (a representative of) `ζ` starting at `e₀`. -/
noncomputable def windEnd (b : Circle) (e₀ : ℝ) (he : Circle.exp e₀ = b)
    (ζ : FundamentalGroup Circle b) : ℝ :=
  (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath ζ) ⟨e₀, he⟩).1

variable {b : Circle} {e₀ : ℝ} (he : Circle.exp e₀ = b)

theorem exp_windEnd (ζ : FundamentalGroup Circle b) :
    Circle.exp (windEnd b e₀ he ζ) = b :=
  (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath ζ) ⟨e₀, he⟩).2

/-- Translation independence of the lift endpoint, at the level of the monodromy action. -/
theorem monodromy_val_sub (ζ : Path.Homotopic.Quotient b b) (e e' : ℝ)
    (he : Circle.exp e = b) (he' : Circle.exp e' = b) :
    (Circle.isCoveringMap_exp.monodromy ζ ⟨e', he'⟩).1 - e'
      = (Circle.isCoveringMap_exp.monodromy ζ ⟨e, he⟩).1 - e := by
  induction ζ using Quotient.ind with
  | _ γ =>
    have hexp : Circle.exp e' = Circle.exp e := by rw [he, he']
    have hstart : (γ : C(I, Circle)) 0 = Circle.exp e := by
      show γ 0 = Circle.exp e; rw [γ.source, he]
    have hstart' : (γ : C(I, Circle)) 0 = Circle.exp e' := by
      show γ 0 = Circle.exp e'; rw [γ.source, he']
    show Circle.isCoveringMap_exp.liftPath _ e' _ 1 - e'
        = Circle.isCoveringMap_exp.liftPath _ e _ 1 - e
    rw [liftPath_apply_one_of_exp_eq (γ : C(I, Circle)) e e' hstart hstart' hexp]
    ring

theorem windEnd_one : windEnd b e₀ he 1 = e₀ := by
  have h1 : FundamentalGroup.toPath (1 : FundamentalGroup Circle b)
      = Path.Homotopic.Quotient.refl b := rfl
  unfold windEnd
  rw [h1, Circle.isCoveringMap_exp.monodromy_refl]
  rfl

/-- The endpoint of the lift starting at any point `e` in the fibre over `b`. -/
theorem monodromy_val_at (ζ : FundamentalGroup Circle b) (e : ℝ)
    (hemem : Circle.exp e = b) :
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath ζ) ⟨e, hemem⟩).1
      = e + (windEnd b e₀ he ζ - e₀) := by
  have h := monodromy_val_sub (FundamentalGroup.toPath ζ) e₀ e he hemem
  have hd : windEnd b e₀ he ζ
      = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath ζ) ⟨e₀, he⟩).1 := rfl
  rw [hd]; linear_combination h

theorem windEnd_mul (ζ θ : FundamentalGroup Circle b) :
    windEnd b e₀ he (ζ * θ) = windEnd b e₀ he θ + windEnd b e₀ he ζ - e₀ := by
  have hmul : FundamentalGroup.toPath (ζ * θ)
      = (FundamentalGroup.toPath θ).trans (FundamentalGroup.toPath ζ) := rfl
  have hθmem : Circle.exp (windEnd b e₀ he θ) = b := exp_windEnd he θ
  have hstep : windEnd b e₀ he (ζ * θ)
      = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath ζ)
          (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath θ) ⟨e₀, he⟩)).1 := by
    unfold windEnd; rw [hmul, Circle.isCoveringMap_exp.monodromy_trans_apply]
  rw [hstep]
  have hinner : Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath θ) ⟨e₀, he⟩
      = ⟨windEnd b e₀ he θ, hθmem⟩ := rfl
  rw [hinner, monodromy_val_at he ζ (windEnd b e₀ he θ) hθmem]
  ring

/-- The winding-number homomorphism on `π₁(Circle, b)`, valued in `ℝ`: the gap
between the endpoints of a lift through `Circle.exp`.  It vanishes exactly on
classes whose lift closes. -/
noncomputable def windingHom (b : Circle) (e₀ : ℝ) (he : Circle.exp e₀ = b) :
    Additive (FundamentalGroup Circle b) →+ ℝ where
  toFun ξ := windEnd b e₀ he (Additive.toMul ξ) - e₀
  map_zero' := by
    show windEnd b e₀ he 1 - e₀ = 0
    rw [windEnd_one he]; ring
  map_add' ξ η := by
    show windEnd b e₀ he (Additive.toMul ξ * Additive.toMul η) - e₀
        = (windEnd b e₀ he (Additive.toMul ξ) - e₀) + (windEnd b e₀ he (Additive.toMul η) - e₀)
    rw [windEnd_mul he]; ring

@[simp] theorem windingHom_apply (ξ : Additive (FundamentalGroup Circle b)) :
    windingHom b e₀ he ξ = windEnd b e₀ he (Additive.toMul ξ) - e₀ := rfl

end CircleLift

/-! ## Engine 1: crossing-parity via hom-triviality -/

variable {X : Type*} [TopologicalSpace X]

/-- **Winding of a lifted loop through a hom-trivial space vanishes.**
For a continuous `τ : X → Circle`, a loop `δ : Path x x` in a space `X` with
`HomTrivialSpace X`, and any continuous real lift `Λ` of `τ ∘ δ`, the lift is a
loop: `Λ 1 = Λ 0`.  This is the hom-trivial analog of
`lift_endpoint_eq_of_simplyConnected`. -/
theorem lift_endpoint_eq_of_homTrivial (hX : HomTrivialSpace X)
    {τ : X → Circle} (hτ : Continuous τ) {x : X} (δ : Path x x)
    (Λ : C(I, ℝ)) (hlift : ∀ t, Circle.exp (Λ t) = τ (δ t)) :
    Λ 1 = Λ 0 := by
  set cov := Circle.isCoveringMap_exp with hcov
  set τc : C(X, Circle) := ⟨τ, hτ⟩ with hτc
  set b : Circle := τ x with hb
  set e₀ : ℝ := Λ 0 with he₀
  have hδ0 : δ 0 = x := δ.source
  have he : Circle.exp e₀ = b := by
    show Circle.exp (Λ 0) = τ x
    rw [hlift 0, hδ0]
  -- `sc = τ ∘ δ` as a loop at `b`
  set sc : Path b b := δ.map τc.continuous with hsc
  have hcomp : (⇑Circle.exp) ∘ (Λ : I → ℝ) = (sc : I → Circle) := by
    funext t
    show Circle.exp (Λ t) = sc t
    exact hlift t
  have hsc0 : (sc : C(I, Circle)) 0 = Circle.exp e₀ := by
    show sc 0 = Circle.exp (Λ 0)
    exact (hlift 0).symm
  have hΛlift : (Λ : C(I, ℝ)) = cov.liftPath sc e₀ hsc0 :=
    (cov.eq_liftPath_iff' hsc0).mpr ⟨hcomp, rfl⟩
  -- the class of `δ` as a genuine fundamental-group element (clean type for `ofMul`)
  set ζ : FundamentalGroup X x := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ) with hζ
  -- `τ⁎ ζ` is represented by `sc`
  have hmapδ : FundamentalGroup.map τc x ζ
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk sc) := rfl
  have hwind : CircleLift.windEnd b e₀ he (FundamentalGroup.map τc x ζ) = Λ 1 := by
    rw [hmapδ, hΛlift]; rfl
  -- the winding hom vanishes by hom-triviality
  haveI := hX x
  have hW : (CircleLift.windingHom b e₀ he).comp (FundamentalGroup.map τc x).toAdditive = 0 :=
    Subsingleton.elim _ _
  have hval := DFunLike.congr_fun hW (Additive.ofMul ζ)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toAdditive, toMul_ofMul,
    AddMonoidHom.zero_apply, CircleLift.windingHom_apply] at hval
  rw [hwind] at hval
  linarith

/-! ## Engines 2 and 3: open ↔ closed transfer for a level piece -/

section Chart
open Rado
variable [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Open ↔ closed transfer for hom-trivial loops.**  If `V` is an open level-set
piece with a harmonic straightening collar (dichotomy `hdich`, level `hfc`, chart
germs `hchart`) whose closure has hom-trivial loops, then `V` itself has
hom-trivial loops.  This is the hom-trivial analog of `isSimplyConnected_of_closure`. -/
theorem homTrivialLoops_of_closure_push [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ}
    (hVo : IsOpen V) (hVcl : IsCompact (closure V))
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hclV : HomTrivialSpace ↥(closure V)) :
    HomTrivialLoops V := by
  intro v₀ hv₀
  set a : ↥V := ⟨v₀, hv₀⟩ with ha
  refine ⟨fun φ ψ => AddMonoidHom.ext fun α => ?_⟩
  suffices hzero : ∀ (χ : Additive (FundamentalGroup ↥V a) →+ ℝ), χ α = 0 by
    rw [hzero φ, hzero ψ]
  intro χ
  obtain ⟨ζ, rfl⟩ := (Additive.ofMul (α := FundamentalGroup ↥V a)).surjective α
  induction ζ using Quotient.ind with
  | _ γ =>
    -- the push fixing the loop `γ`
    set L : Set X := Set.range (fun t : I => ((γ t : ↥V) : X)) with hL
    have hLcont : Continuous (fun t : I => ((γ t : ↥V) : X)) :=
      continuous_subtype_val.comp γ.continuous
    have hLc : IsCompact L := isCompact_range hLcont
    have hLV : L ⊆ V := by rintro _ ⟨t, rfl⟩; exact (γ t).2
    obtain ⟨g, hgV, hgid⟩ := exists_push_into hVo hVcl hdich hfc hchart hLc hLV
    have hgloop : ∀ t, g ((γ t : ↥V) : X) = ((γ t : ↥V) : X) := fun t => hgid _ ⟨t, rfl⟩
    have hv0mem : v₀ ∈ L := ⟨0, by show ((γ 0 : ↥V) : X) = v₀; rw [γ.source, ha]⟩
    have hgv0 : g v₀ = v₀ := hgid v₀ hv0mem
    -- inclusion `V → closure V` and corestricted push `closure V → V`
    set ιmap : C(↥V, ↥(closure V)) := ⟨Set.inclusion subset_closure, continuous_inclusion _⟩
      with hιmap
    set Gmap : C(↥(closure V), ↥V) := ⟨fun y => ⟨g y.1, hgV y.1 y.2⟩,
      Continuous.subtype_mk (g.continuous.comp continuous_subtype_val)
        (fun y => hgV y.1 y.2)⟩ with hGmap
    have hGa : Gmap (ιmap a) = a := by
      apply Subtype.ext
      show g v₀ = v₀
      exact hgv0
    -- the composite `(closure-push) ∘ (inclusion)` fixes the class of `γ`
    have key : FundamentalGroup.mapOfEq Gmap hGa (FundamentalGroup.map ιmap a ⟦γ⟧) = ⟦γ⟧ := by
      rw [show FundamentalGroup.map ιmap a ⟦γ⟧
            = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ.map ιmap.continuous)) from
          rfl, FundamentalGroup.mapOfEq_apply]
      have hpaths :
          ((γ.map ιmap.continuous).map Gmap.continuous).cast hGa.symm hGa.symm = γ := by
        ext t
        exact hgloop t
      rw [hpaths]
      rfl
    -- pull an arbitrary hom back along the closure-push and kill it
    haveI := hclV (ιmap a)
    have hpull : χ.comp (FundamentalGroup.mapOfEq Gmap hGa).toAdditive = 0 := Subsingleton.elim _ _
    have hstep := DFunLike.congr_fun hpull (Additive.ofMul (FundamentalGroup.map ιmap a ⟦γ⟧))
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toAdditive,
      toMul_ofMul, AddMonoidHom.zero_apply] at hstep
    rw [key] at hstep
    exact hstep

/-- **Retract corollary for hom-trivial loops (W8/F3 step L8/L9).**  If `X` has
hom-trivial loops and `r : X → X` is a continuous retraction onto `closure V`
(landing in and fixing `closure V`), then the open level piece `V` has hom-trivial
loops.  Combines `homTrivialSpace_of_retract` with `homTrivialLoops_of_closure_push`. -/
theorem homTrivialLoops_of_retract_closure [T2Space X] {V : Set X} {f : X → ℝ} {c : ℝ}
    (hVo : IsOpen V) (hVcl : IsCompact (closure V))
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hX : HomTrivialSpace X)
    (r : C(X, X)) (hrA : ∀ x, r x ∈ closure V) (hrid : ∀ y ∈ closure V, r y = y) :
    HomTrivialLoops V := by
  have hclV : HomTrivialSpace ↥(closure V) :=
    homTrivialSpace_of_retract
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(closure V), X))
      (⟨fun x => ⟨r x, hrA x⟩, r.continuous.subtype_mk hrA⟩ : C(X, ↥(closure V)))
      (fun a => Subtype.ext (hrid a.1 a.2)) hX
  exact homTrivialLoops_of_closure_push hVo hVcl hdich hfc hchart hclV

end Chart

end Uniformization
