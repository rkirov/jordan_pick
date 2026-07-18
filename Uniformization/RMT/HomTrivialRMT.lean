/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.RMT.RiemannMapping
import Uniformization.RMT.HomTrivial

/-!
# Riemann mapping theorem under a hom-trivial hypothesis

This file mirrors the ported Riemann-mapping chain of `Uniformization/RMT/RiemannMapping.lean`,
replacing the `IsSimplyConnected U` hypothesis with the weaker `HomTrivialLoops U` (plus
`IsConnected U`).  The `IsSimplyConnected` hypothesis is used in the ported proofs only

* to construct branches of `log` / `n`-th roots (now supplied by
  `Complex.exists_branch_log_of_homTrivial` / `exists_branch_nthRoot_of_homTrivial`), and
* for preconnectedness of `U` (now supplied by `IsConnected U`).

The `wlog` translation step in `exists_mapsTo_unitBall_injOn_deriv_ne_zero` requires transporting
`HomTrivialLoops` along the translation homeomorphism, handled by `HomTrivialLoops.vadd`.

Main result: `Complex.exists_bijOn_unitBall_map_eq_zero_of_homTrivial`.
-/

open Set Metric Function Filter
open scoped Pointwise Topology ComplexConjugate Real BigOperators Uniformity

/-- Hom-triviality of loops is invariant under translation. -/
theorem HomTrivialLoops.vadd {U : Set ℂ} (c : ℂ) (h : HomTrivialLoops U) :
    HomTrivialLoops (c +ᵥ U) := by
  have hset : (Homeomorph.addLeft c) '' U = c +ᵥ U := by
    ext z
    simp only [Set.mem_image, Set.mem_vadd_set, Homeomorph.coe_addLeft, vadd_eq_add]
  exact h.of_homeomorph
    ((Homeomorph.image (Homeomorph.addLeft c) U).trans (Homeomorph.setCongr hset))

namespace Complex

namespace UnitDisc

/-- `n`-th root branch into the unit disc, hom-trivial version of
`Complex.UnitDisc.exists_branch_nthRoot`. -/
protected theorem exists_branch_nthRoot_of_homTrivial {X : Type*} [TopologicalSpace X]
    [LocPathConnectedSpace X] {U : Set X} (hUt : HomTrivialLoops U) (hUconn : IsConnected U)
    (hUo : IsOpen U) {g : X → UnitDisc} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) (n : ℕ+) :
    ∃ f : X → UnitDisc, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  rcases exists_branch_nthRoot_of_homTrivial hUt hUconn hUo
    (continuous_coe.comp_continuousOn hgc)
    (by simpa using hU₀) n.ne_zero with ⟨f, hfc, hf⟩
  suffices ∀ x, ‖f x‖ < 1 by
    lift f to X → 𝔻 using this
    refine ⟨f, isEmbedding_coe.continuousOn_iff.mpr hfc, fun x ↦ ?_⟩
    simpa only [← coe_pow, Function.comp_apply, coe_inj] using hf x
  intro x
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) n.ne_zero, ← norm_pow, hf]
  exact (g x).norm_lt_one

end UnitDisc

/-- Hom-trivial version of `Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero`. -/
theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_homTrivial {U : Set ℂ} (hUo : IsOpen U)
    (hUt : HomTrivialLoops U) (hUconn : IsConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    have hUconn' : IsConnected ((-a) +ᵥ U) := by
      rw [← Set.image_vadd]
      exact hUconn.image _ (continuous_const_vadd (-a)).continuousOn
    specialize this (hUo.vadd (-a)) (hUt.vadd (-a)) hUconn' (by simp [hU]) (x := -a + x)
      (by simpa [mem_vadd_set_iff_neg_vadd_mem]) (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf₁, hf_inj, hdf⟩
    refine ⟨f ∘ (-a + ·), hf₁.comp (mapsTo_image _ _),
      hf_inj.comp (by simp [InjOn]) (mapsTo_image _ _), fun z hz ↦ ?_⟩
    simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)
  rcases exists_branch_nthRoot_of_homTrivial hUt hUconn hUo continuousOn_id (by rwa [image_id])
    two_ne_zero with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  have hdf' : DifferentiableOn ℂ f U := fun z hz ↦
    (hdf z hz).hasDerivAt.differentiableAt.differentiableWithinAt
  have hfUx : f '' U ∈ 𝓝 (f x) := by
    rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
    exact Filter.image_mem_map <| hUo.mem_nhds hx
  have hdisj : ∀ a ∈ U, ∀ b ∈ U, f a + f b ≠ 0 := by
    intro a ha b hb hfab
    obtain rfl : b = a := by
      rw [← hf_inv a, ← hf_inv b]
      simp [eq_neg_iff_add_eq_zero.mpr hfab]
    have : f b = 0 := by linear_combination hfab / 2
    exact hf₀ b hb this
  have hfUxc : (f '' U)ᶜ ∈ 𝓝 (-f x) := by
    rw [nhds_neg, Filter.mem_neg]
    filter_upwards [hfUx]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hdisj a ha b hb (by linear_combination hab)
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hfUxc with ⟨ε, hε₀, hε⟩
  use fun z ↦ ε / (f x + f z)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · by_contra! hle
      refine @hε (f z) ?_ (mem_image_of_mem f hz)
      simpa [dist_eq_norm, add_comm] using hle
    · simpa using hdisj x hx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inv.injective.eq_iff] using heq
  case deriv =>
    intro z hz
    rw [(hasDerivAt_const _ _).fun_div ((hdf z hz).hasDerivAt.const_add _) _ |>.deriv]
    · simp [hε₀.ne', hf₀ z hz, hdisj x hx z hz]
    · exact hdisj x hx z hz

/-- Hom-trivial version of `Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀`. -/
theorem exists_map_unitDisc_injOn_deriv_ne_zero₀_of_homTrivial {U : Set ℂ} (hUo : IsOpen U)
    (hUt : HomTrivialLoops U) (hUconn : IsConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → UnitDisc, f x = 0 ∧ InjOn f U ∧ (∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0) := by
  classical
  obtain ⟨f, hf_inj, hf_deriv⟩ :
      ∃ f : ℂ → UnitDisc, InjOn f U ∧ ∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0 := by
    rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_homTrivial hUo hUt hUconn hU hx
      with ⟨f, hfU, hf_inj, hdf⟩
    use fun z ↦ if hz : z ∈ U then .mk (f z) (by simpa using hfU hz) else 0
    constructor
    · simp +contextual [InjOn, UnitDisc.mk_inj, hf_inj.eq_iff]
    · intro z hz
      convert hdf z hz using 1
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hUo.mem_nhds hz] with w hw
      simp [hw]
  use fun z ↦ (-f x).shift (f z)
  refine ⟨?map_x, (-f x).shift.injective.comp_injOn hf_inj, ?deriv⟩
  case map_x => simp
  case deriv =>
    simpa only [Function.comp_def, ne_eq, UnitDisc.deriv_shift_comp_eq_zero]

/-- Hom-trivial version of `Complex.exist_map_unitDisc_injOn_norm_deriv_gt`. -/
theorem exist_map_unitDisc_injOn_norm_deriv_gt_of_homTrivial {U : Set ℂ} (hUo : IsOpen U)
    (hUt : HomTrivialLoops U) (hUconn : IsConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U)
    {f : ℂ → UnitDisc} (hdf : DifferentiableOn ℂ (UnitDisc.coe ∘ f) U) (hf₀ : f x = 0)
    (hf_inj : InjOn f U) (hsurj : ¬SurjOn f U univ) :
    ∃ g : ℂ → UnitDisc, g x = 0 ∧ InjOn g U ∧ DifferentiableOn ℂ (UnitDisc.coe ∘ g) U ∧
      ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ g) x‖ := by
  by_cases hdf₀ : deriv (UnitDisc.coe ∘ f) x = 0
  · rcases exists_map_unitDisc_injOn_deriv_ne_zero₀_of_homTrivial hUo hUt hUconn hU hx
      with ⟨g, hg₀, hg_inj, hdg⟩
    refine ⟨g, hg₀, hg_inj, fun z hz ↦ ?_, ?_⟩
    · exact (differentiableAt_of_deriv_ne_zero (hdg z hz)).differentiableWithinAt
    · simpa [hdf₀] using hdg x hx
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by simpa [SurjOn, eq_univ_iff_forall] using hsurj
  have hcf : ContinuousOn f U := by
    rw [UnitDisc.isEmbedding_coe.continuousOn_iff]
    exact hdf.continuousOn
  rcases UnitDisc.exists_branch_nthRoot_of_homTrivial hUt hUconn hUo
    ((-c).continuous_shift.comp_continuousOn hcf) (by simpa) 2 with ⟨g, hgc, hgf⟩
  have hg₀ : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    suffices g z ^ (2 : ℕ+) ≠ 0 by simpa using this
    simp [hgf, hc z hz]
  have hdg : ∀ z ∈ U, HasDerivAt (g · : ℂ → ℂ)
      ((1 - ‖(c : ℂ)‖ ^ 2) / (2 * g z * (1 - conj ↑c * f z) ^ 2) * deriv (f · : ℂ → ℂ) z) z := by
    intro z hz
    refine ((hasDerivAt_pow 2 _).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (UnitDisc.hasDerivAt_shift_comp _ <| (hdf.hasDerivAt <| hUo.mem_nhds hz))
      (by simp [hg₀ z hz])
      (.of_forall fun x ↦ congr(UnitDisc.coe $(hgf x)))).congr_deriv ?_
    simp [Function.comp_def, field]
    ring
  have hg_sq_norm (z : ℂ) : ‖(g z : ℂ)‖ ^ 2 = ‖((-c).shift (f z) : ℂ)‖ := by
    rw [← norm_pow, ← PNat.val_ofNat, ← UnitDisc.coe_pow, hgf, Function.comp_apply]
  have hg_norm (z : ℂ) : ‖(g z : ℂ)‖ = √‖((-c).shift (f z) : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), hg_sq_norm]
  refine ⟨(-g x).shift ∘ g, ?map_x, ?injOn, ?deriv, ?norm_deriv⟩
  case map_x => simp
  case injOn =>
    refine (-g x).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_
    simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  case deriv =>
    exact (-g x).differentiableOn_shift_comp_iff.mpr fun z hz ↦
      (hdg z hz).differentiableAt.differentiableWithinAt
  case norm_deriv =>
    have hkey : ‖deriv (UnitDisc.coe ∘ ⇑(-g x).shift ∘ g) x‖ =
        ‖deriv (f · : ℂ → ℂ) x‖ * (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgx : ‖(g x : ℂ)‖ = √‖(c : ℂ)‖ := by simp [hg_norm, hf₀]
      simp only [Function.comp_def, UnitDisc.deriv_shift_comp, (hdg x hx).deriv, norm_mul, norm_div,
        ← mul_assoc, conj_mul', UnitDisc.coe_neg, map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.2 c.norm_lt_one
      have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.2 c.sq_norm_lt_one
      simp [field, hgx, hf₀, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hdf₀
    · have hc₀ : 0 < ‖(c : ℂ)‖ := by simpa [hf₀] using (hc x hx).symm
      suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
      have : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at this
      · linear_combination this
      · apply norm_nonneg

open scoped UniformConvergence in
/-- Riemann mapping theorem under a hom-trivial hypothesis: `U` open, connected, with hom-trivial
loops and `U ≠ univ`, admits a biholomorphism onto the unit ball sending `x₀` to `0`. -/
theorem exists_bijOn_unitBall_map_eq_zero_of_homTrivial {U : Set ℂ} (hUo : IsOpen U)
    (hUt : HomTrivialLoops U) (hUconn : IsConnected U) (hU : U ≠ univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x₀ = 0 := by
  set 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  have h𝔖K : ∀ K ∈ 𝔖, IsCompact K := fun _ ↦ And.right
  have hcnt : (𝓤 (ℂ →ᵤ[𝔖] ℂ)).IsCountablyGenerated := by
    have := hUo.locallyCompactSpace
    have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
    set φ : CompactExhaustion U := default
    apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n ↦ (↑) '' φ n)
    · intro n
      exact ⟨image_val_subset, φ.isCompact n |>.image continuous_subtype_val⟩
    · exact monotone_image.comp φ.subset
    · rintro K ⟨hKU, hKc⟩
      lift K to Set U using hKU
      rw [← Subtype.isCompact_iff] at hKc
      exact (φ.exists_superset_of_isCompact hKc).imp fun n hn ↦ by gcongr
  set F : (ℂ →ᵤ[𝔖] ℂ) → (ℂ → ℂ) := fun f ↦ UniformOnFun.toFun _ f
  have hF : ∀ {f : ℂ →ᵤ[𝔖] ℂ} {s}, TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := by
    intro f s
    have : Tendsto id (𝓝[s] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using this
  set s : Set (ℂ →ᵤ[𝔖] ℂ) :=
    {f : ℂ →ᵤ[𝔖] ℂ |
      MapsTo (F f) U (ball 0 1) ∧
      InjOn (F f) U ∧
      DifferentiableOn ℂ (F f) U ∧
      deriv (F f) x₀ ≠ 0 ∧
      F f x₀ = 0}
  have hsd : ∀ f ∈ s, DifferentiableOn ℂ (F f) U := fun f hf ↦ hf.2.2.1
  have hs_ne : s.Nonempty := by
    rcases exists_map_unitDisc_injOn_deriv_ne_zero₀_of_homTrivial hUo hUt hUconn hU hx₀
      with ⟨f, hf₀, hf_inj, hfd⟩
    exact ⟨UniformOnFun.ofFun 𝔖 (f ·), fun x hx ↦ (f x).2,
      by simpa [F, InjOn] using hf_inj, fun z hz ↦
        differentiableAt_of_deriv_ne_zero (hfd z hz) |>.differentiableWithinAt,
      hfd x₀ hx₀, by simp [F, hf₀]⟩
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖K (α := ℂ) (s := s) (F := F)
    .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    refine equicontinuousAt_of_forall_norm_le (hUo.mem_nhds <| hKU hz) (fun i ↦ hsd _ i.2)
      ⟨1, fun i z hz ↦ le_of_lt ?_⟩ |>.equicontinuousWithinAt _
    simpa using i.2.1 hz
  case bdd =>
    intro K hK x hx
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun i hi ↦
      ball_subset_closedBall <| hi.1 (hK.1 hx)⟩
  have hcl : closure s ⊆
      {f | MapsTo (F f) U (ball 0 1) ∧
           ((∃ C, EqOn (F f) (const ℂ C) U) ∨ InjOn (F f) U) ∧
           DifferentiableOn ℂ (F f) U ∧
           F f x₀ = 0} := by
    intro f hf
    rw [mem_closure_iff_nhdsWithin_neBot] at hf
    have htendsto : TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := hF
    have hdf : DifferentiableOn ℂ (F f) U := htendsto.differentiableOn
      (eventually_mem_nhdsWithin.mono hsd) hUo
    have hf_le : ∀ z ∈ U, ‖F f z‖ ≤ 1 := by
      intro z hz
      refine le_of_tendsto (htendsto.tendsto_at hz).norm <| eventually_mem_nhdsWithin.mono ?_
      intro g hg
      apply le_of_lt
      simpa using hg.1 hz
    have hfx₀ : F f x₀ = 0 := by
      refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
      refine tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
      exact hg.2.2.2.2.symm
    refine ⟨?_, ?_, hdf, hfx₀⟩
    · by_contra hf_ball
      obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
      have : IsMaxOn (‖F f ·‖) U z := by
        intro y hy
        simpa using (hf_le y hy).trans hz
      have : F f x₀ = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        hUconn.isPreconnected hUo hdf hzU this hx₀
      norm_num [← this, hfx₀] at hz
    · exact eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo
        hUconn.isPreconnected
        (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.1)
        (eventually_mem_nhdsWithin.mono hsd)
        htendsto
  have hcont : ContinuousOn (fun f ↦ ‖deriv (F f) x₀‖) (closure s) := by
    refine .mono (.norm fun f hf ↦ ?_) hcl
    refine TendstoLocallyUniformlyOn.tendsto_at (.deriv hF ?_ hUo) hx₀
    refine eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
    exact hg.2.2.1
  rcases hcmpct.exists_isMaxOn hs_ne.closure hcont with ⟨f₀, hf₀_mem, hf₀_max⟩
  have hdf₀_x₀ : 0 < ‖deriv (F f₀) x₀‖ := by
    rcases hs_ne with ⟨f', hf'⟩
    refine lt_of_lt_of_le ?_ (hf₀_max <| subset_closure hf')
    simpa using hf'.2.2.2.1
  rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hf₀_diff, hf₀_x₀⟩
  replace hf₀_inj : InjOn (F f₀) U := by
    refine hf₀_inj.resolve_left ?_
    rintro ⟨C, hC⟩
    rw [hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq] at hdf₀_x₀
    unfold const at hdf₀_x₀
    simp at hdf₀_x₀
  refine ⟨F f₀, hf₀_diff, ⟨hf₀_mapsTo, hf₀_inj, ?_⟩, hf₀_x₀⟩
  by_contra! hsurj
  clear hf₀_mem hdf₀_x₀
  rw [isMaxOn_iff] at hf₀_max
  wlog hf₀_lt : ∀ z, ‖F f₀ z‖ < 1 generalizing f₀
  · classical
    apply this (UniformOnFun.ofFun _ <| U.indicator (F f₀))
    · have : deriv (U.indicator (F f₀)) x₀ = deriv (F f₀) x₀ :=
        U.eqOn_indicator.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq
      simpa [this, F] using hf₀_max
    · simpa [F, U.eqOn_indicator.mapsTo_iff]
    · simpa [F, differentiableOn_congr U.eqOn_indicator]
    · simp [F, hf₀_x₀]
    · simpa [F, U.eqOn_indicator.injOn_iff]
    · simpa [F, U.eqOn_indicator.surjOn_iff]
    · intro z
      by_cases hz : z ∈ U <;> simp [F, hz, mem_ball_zero_iff.mp (hf₀_mapsTo _)]
  lift F f₀ to ℂ → UnitDisc using hf₀_lt with f hf
  replace hsurj : ¬SurjOn f U univ := by
    simpa [SurjOn, eq_univ_iff_forall, subset_def, UnitDisc.exists, ← UnitDisc.coe_inj] using hsurj
  rcases exist_map_unitDisc_injOn_norm_deriv_gt_of_homTrivial hUo hUt hUconn hU hx₀ hf₀_diff
    (by simpa using hf₀_x₀) (by simpa [InjOn] using hf₀_inj) hsurj with ⟨g, hg₀, hg_inj, hdg, hg_lt⟩
  refine hf₀_max (UniformOnFun.ofFun _ (g · : ℂ → ℂ)) (subset_closure ?_) |>.not_gt hg_lt
  refine ⟨fun z _ ↦ (g z).2, by simpa [F, InjOn] using hg_inj, hdg, ?_, by simpa [F] using hg₀⟩
  rw [← norm_pos_iff]
  exact (norm_nonneg _).trans_lt hg_lt

end Complex
