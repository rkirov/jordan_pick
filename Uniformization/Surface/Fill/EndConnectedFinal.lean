/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.CrossPhase
import Uniformization.Surface.Fill.EndConnected
import Uniformization.Surface.Fill.Parity
import Uniformization.Surface.Fill.BoundaryCircle

/-!
# End-frontier connectivity: the crossing-parity contradiction (W7 step L5.4c)

For a connected piece `V` whose closure is compact, this file completes the
crossing-parity argument and proves that every complement end
`Z = connectedComponentIn (closure V)ᶜ x` has **preconnected frontier**.

The proof is by contradiction.  If `frontier Z` splits into two relatively clopen
nonempty parts, then (via `EndConnected`) it contains two *distinct* whole
components `C ≠ C'` of `frontier V`.  Attaching the crossing phase `τ` of `C`
(`CrossPhase.exists_crossingPhase`), we build a loop `L` (base point on the
`Z`-side of `C`) that runs through `Z` to the `Z`-side of `C'`, crosses `C'`
into `V` (a region where `τ ≡ 1`), runs back through `V`, and crosses `C` back
to the base point.

Two sided real functions `liftZ, liftV : X → ℝ` both lift `τ` (`exp ∘ liftZ = τ =
exp ∘ liftV`), are continuous on complementary collar-avoiding open sets, and
differ by `2π` inside the collar `N` of `C`.  Gluing `liftZ` along the first half
of `L` and `liftV` along the second half gives an explicit continuous lift `Λ` of
`τ ∘ L` whose endpoints differ by `2π`.  But `lift_endpoint_eq_of_simplyConnected`
forces `Λ 1 = Λ 0` — the contradiction.
-/

open Set Metric Topology Filter
open scoped unitInterval

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Transversal crossing data at a frontier point of a complement end -/

/-- **Transversal crossing segment.**  At a point `ξ` of `frontier Z`
(`Z = connectedComponentIn (closure V)ᶜ x₀`), inside any open neighbourhood `G`
of `ξ`, there is a short straight segment crossing `frontier V` at `ξ`: a path
`seg` from a `V`-side endpoint `v ∈ V` to a `Z`-side endpoint `z ∈ Z`, staying in
`G`, with the collar coordinate reading `f (seg t) = c + η (1 - 2t)`.  The
half-width `η` can be taken below any prescribed `μ`. -/
theorem crossing_data [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x₀ ξ : X} (hξ : ξ ∈ frontier (connectedComponentIn (closure V)ᶜ x₀))
    {G : Set X} (hGo : IsOpen G) (hξG : ξ ∈ G) {μ : ℝ} (hμ : 0 < μ) :
    ∃ (z v : X) (η : ℝ) (seg : Path v z), 0 < η ∧ η < μ ∧
      z ∈ connectedComponentIn (closure V)ᶜ x₀ ∧ v ∈ V ∧
      (∀ t, seg t ∈ G) ∧ (∀ t, f (seg t) = c + η * (1 - 2 * (t : ℝ))) := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  set Z := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  have hZcompl : Z ⊆ (closure V)ᶜ := connectedComponentIn_subset _ _
  have hξfrV : ξ ∈ frontier V := frontier_component_compl_closure_subset hξ
  obtain ⟨ψ, δbox, εbox, hψ, hξψ, hδbox, hεbox, hqre, hbox_tgt, hWopen, hξW,
    hf_eq, hVeq, hfront⟩ := exists_straight_box hVo hdich hfc hchart hξfrV
  set q := ψ ξ with hq
  set box := straightBox q c δbox εbox with hboxdef
  set W := ψ.symm '' box with hWdef
  have hboxopen : IsOpen box := by rw [hboxdef]; exact isOpen_straightBox q c δbox εbox
  have hqtgt : q ∈ ψ.target := ψ.map_source hξψ
  have hqbox : q ∈ box := by
    rw [hboxdef, mem_straightBox]
    exact ⟨by rw [hqre, sub_self, abs_zero]; exact hδbox,
      by rw [sub_self, abs_zero]; exact hεbox⟩
  have hcl : closure V = V ∪ frontier V := by
    rw [hVo.frontier_eq]; exact (Set.union_sdiff_cancel subset_closure).symm
  have hmemV : ∀ w ∈ box, c < w.re → ψ.symm w ∈ closure V := by
    intro w hw hlt
    have : ψ.symm w ∈ V ∩ W := by rw [hVeq]; exact ⟨w, ⟨hw, hlt⟩, rfl⟩
    exact subset_closure this.1
  have hmemF : ∀ w ∈ box, w.re = c → ψ.symm w ∈ closure V := by
    intro w hw heq
    have : ψ.symm w ∈ frontier V ∩ W := by rw [hfront]; exact ⟨w, ⟨hw, heq⟩, rfl⟩
    exact frontier_subset_closure this.1
  have hloNotClV : ∀ w ∈ box, w.re < c → ψ.symm w ∉ closure V := by
    intro w hw hlt hmem
    rw [hcl] at hmem
    rcases hmem with hV | hF
    · have hmem2 : ψ.symm w ∈ V ∩ W := ⟨hV, w, hw, rfl⟩
      rw [hVeq] at hmem2
      obtain ⟨w', ⟨hw', hw'lt⟩, hww'⟩ := hmem2
      have e1 : f (ψ.symm w) = w.re := hf_eq w hw
      have e2 : f (ψ.symm w') = w'.re := hf_eq w' hw'
      rw [hww'] at e2; rw [e1] at e2
      rw [← e2] at hw'lt
      exact absurd hw'lt (not_lt.mpr (le_of_lt hlt))
    · have hmem2 : ψ.symm w ∈ frontier V ∩ W := ⟨hF, w, hw, rfl⟩
      rw [hfront] at hmem2
      obtain ⟨w', ⟨hw', hw'eq⟩, hww'⟩ := hmem2
      have e1 : f (ψ.symm w) = w.re := hf_eq w hw
      have e2 : f (ψ.symm w') = w'.re := hf_eq w' hw'
      rw [hww'] at e2; rw [e1] at e2
      rw [hw'eq] at e2
      rw [e2] at hlt; exact lt_irrefl c hlt
  have hboxconv : Convex ℝ box := by
    have hbox_eq : box = ({z : ℂ | z.re < c + δbox} ∩ {z : ℂ | c - δbox < z.re}) ∩
        ({z : ℂ | z.im < q.im + εbox} ∩ {z : ℂ | q.im - εbox < z.im}) := by
      ext w
      simp only [hboxdef, straightBox, mem_ofPred_eq, mem_inter_iff, abs_lt]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    rw [hbox_eq]
    exact ((convex_halfSpace_re_lt _).inter (convex_halfSpace_re_gt _)).inter
      ((convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _))
  set Lo := box ∩ {w : ℂ | w.re < c} with hLodef
  have hLoconv : Convex ℝ Lo := hboxconv.inter (convex_halfSpace_re_lt c)
  have hLopre : IsPreconnected (ψ.symm '' Lo) := by
    have hcont : ContinuousOn ψ.symm Lo := ψ.continuousOn_symm.mono (fun w hw => hbox_tgt hw.1)
    exact hLoconv.isPreconnected.image _ hcont
  have hLoClV : ψ.symm '' Lo ⊆ (closure V)ᶜ := by
    rintro _ ⟨w, ⟨hw, hwlt⟩, rfl⟩
    exact hloNotClV w hw hwlt
  have hξZbar : ξ ∈ closure Z := frontier_subset_closure hξ
  obtain ⟨p, hpW, hpZ⟩ := _root_.mem_closure_iff.1 hξZbar W hWopen hξW
  obtain ⟨wp, hwp, hpeq⟩ := hpW
  have hpClV : p ∉ closure V := hZcompl hpZ
  have hwplt : wp.re < c := by
    rcases lt_trichotomy wp.re c with h | h | h
    · exact h
    · exact absurd (hpeq ▸ hmemF wp hwp h) hpClV
    · exact absurd (hpeq ▸ hmemV wp hwp h) hpClV
  have hpLo : p ∈ ψ.symm '' Lo := ⟨wp, ⟨hwp, hwplt⟩, hpeq⟩
  have hLoZ : ψ.symm '' Lo ⊆ Z := by
    have hsub := hLopre.subset_connectedComponentIn hpLo hLoClV
    have heq := connectedComponentIn_eq (hZdef ▸ hpZ)
    rw [hZdef, heq]; exact hsub
  have hgtend : Filter.Tendsto (fun s : ℝ => q + (s : ℂ)) (𝓝 0) (𝓝 q) := by
    have hc : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.tendsto 0
    have h := hc.const_add q
    simpa using h
  have hsymmtend : Filter.Tendsto ψ.symm (𝓝 q) (𝓝 ξ) := by
    have hcc := ψ.continuousAt_symm hqtgt
    rw [ContinuousAt, ψ.left_inv hξψ] at hcc
    exact hcc
  have htend : Filter.Tendsto (fun s : ℝ => ψ.symm (q + (s : ℂ))) (𝓝 0) (𝓝 ξ) :=
    hsymmtend.comp hgtend
  have hE1 : (fun s : ℝ => ψ.symm (q + (s : ℂ))) ⁻¹' G ∈ 𝓝 (0 : ℝ) :=
    htend (hGo.mem_nhds hξG)
  have hE2 : (fun s : ℝ => q + (s : ℂ)) ⁻¹' box ∈ 𝓝 (0 : ℝ) :=
    hgtend (hboxopen.mem_nhds hqbox)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hE1 hE2)
  set η := min (μ / 2) (ρ / 2) with hηdef
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  have hημ : η < μ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηρ : η < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsprop : ∀ s : ℝ, |s| ≤ η → ψ.symm (q + (s : ℂ)) ∈ G ∧ q + (s : ℂ) ∈ box := by
    intro s hs
    have hsball : s ∈ Metric.ball (0 : ℝ) ρ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith
    have hmem := hρsub hsball
    exact ⟨hmem.1, hmem.2⟩
  have hst_abs : ∀ t : I, |η * (1 - 2 * (t : ℝ))| ≤ η := by
    intro t
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    rw [abs_mul, abs_of_pos hηpos]
    have hle1 : |1 - 2 * (t : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc η * |1 - 2 * (t : ℝ)| ≤ η * 1 := mul_le_mul_of_nonneg_left hle1 (le_of_lt hηpos)
      _ = η := mul_one η
  have hargbox : ∀ t : I, q + (Complex.ofReal (η * (1 - 2 * (t : ℝ)))) ∈ box :=
    fun t => (hsprop _ (hst_abs t)).2
  have hargG : ∀ t : I, ψ.symm (q + (Complex.ofReal (η * (1 - 2 * (t : ℝ))))) ∈ G :=
    fun t => (hsprop _ (hst_abs t)).1
  have hre : ∀ t : I, (q + (Complex.ofReal (η * (1 - 2 * (t : ℝ))))).re = c + η * (1 - 2 * (t : ℝ)) := by
    intro t; rw [Complex.add_re, Complex.ofReal_re, hqre]
  have hsegcont : Continuous (fun t : I => ψ.symm (q + (Complex.ofReal (η * (1 - 2 * (t : ℝ)))))) :=
    ψ.continuousOn_symm.comp_continuous
      (by fun_prop : Continuous (fun t : I => q + (Complex.ofReal (η * (1 - 2 * (t : ℝ))))))
      (fun t => hbox_tgt (hargbox t))
  set segFun : C(I, X) := ⟨fun t => ψ.symm (q + (Complex.ofReal (η * (1 - 2 * (t : ℝ))))), hsegcont⟩
    with hsegFunDef
  have hs0 : η * (1 - 2 * ((0 : I) : ℝ)) = η := by rw [Set.Icc.coe_zero]; ring
  have hs1 : η * (1 - 2 * ((1 : I) : ℝ)) = -η := by rw [Set.Icc.coe_one]; ring
  refine ⟨segFun 1, segFun 0, η, ⟨segFun, rfl, rfl⟩, hηpos, hημ, ?_, ?_, ?_, ?_⟩
  · have hre1 : (q + (Complex.ofReal (η * (1 - 2 * ((1 : I) : ℝ))))).re < c := by
      rw [hre 1, hs1]; linarith
    exact hLoZ ⟨q + (Complex.ofReal (η * (1 - 2 * ((1 : I) : ℝ)))), ⟨hargbox 1, hre1⟩, rfl⟩
  · have hre0 : c < (q + (Complex.ofReal (η * (1 - 2 * ((0 : I) : ℝ))))).re := by
      rw [hre 0, hs0]; linarith
    have hmem : segFun 0 ∈ V ∩ W := by
      rw [hVeq]; exact ⟨q + (Complex.ofReal (η * (1 - 2 * ((0 : I) : ℝ)))), ⟨hargbox 0, hre0⟩, rfl⟩
    exact hmem.1
  · intro t; exact hargG t
  · intro t
    have h := hf_eq (q + (Complex.ofReal (η * (1 - 2 * (t : ℝ))))) (hargbox t)
    rw [hre t] at h; exact h

/-! ## The crossing-parity contradiction -/

/-- **Preconnected frontier of a complement end.**  Under the piece hypotheses,
with `V` connected and the ambient space simply connected, every complement end
`Z = connectedComponentIn (closure V)ᶜ x` has preconnected frontier.  This is the
crossing-parity capstone (W7 step L5.4c). -/
theorem isPreconnected_frontier_component_compl_closure [T2Space X] [SimplyConnectedSpace X]
    {V : Set X} (hVo : IsOpen V) (hVcl : IsCompact (closure V)) (hVconn : IsConnected V)
    {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x : X} (hx : x ∈ (closure V)ᶜ) :
    IsPreconnected (frontier (connectedComponentIn (closure V)ᶜ x)) := by
  classical
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  have : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have hZopen : IsOpen (connectedComponentIn (closure V)ᶜ x) :=
    isClosed_closure.isOpen_compl.connectedComponentIn
  have hZcompl : connectedComponentIn (closure V)ᶜ x ⊆ (closure V)ᶜ :=
    connectedComponentIn_subset _ _
  have hZconn : IsConnected (connectedComponentIn (closure V)ᶜ x) :=
    ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
  have hZpc : IsPathConnected (connectedComponentIn (closure V)ᶜ x) :=
    (hZopen.isConnected_iff_isPathConnected).mp hZconn
  have hVpc : IsPathConnected V := (hVo.isConnected_iff_isPathConnected).mp hVconn
  by_contra hnp
  rw [isPreconnected_iff_subset_of_disjoint] at hnp
  push Not at hnp
  obtain ⟨u, v, hu, hv, hsub_uv, hdisj, hnotu, hnotv⟩ := hnp
  obtain ⟨ξ, hξfrZ, hξnu⟩ := Set.not_subset.mp hnotu
  obtain ⟨ξ', hξ'frZ, hξ'nv⟩ := Set.not_subset.mp hnotv
  have hξv : ξ ∈ v := (hsub_uv hξfrZ).resolve_left hξnu
  have hξ'u : ξ' ∈ u := (hsub_uv hξ'frZ).resolve_right hξ'nv
  have hξfrV : ξ ∈ frontier V := frontier_component_compl_closure_subset hξfrZ
  have hξ'frV : ξ' ∈ frontier V := frontier_component_compl_closure_subset hξ'frZ
  set C := connectedComponentIn (frontier V) ξ with hCdef
  set C' := connectedComponentIn (frontier V) ξ' with hC'def
  have hC_sub : C ⊆ frontier (connectedComponentIn (closure V)ᶜ x) :=
    frontier_component_compl_closure_component_subset hVo hdich hfc hchart hξfrZ
  have hC'_sub : C' ⊆ frontier (connectedComponentIn (closure V)ᶜ x) :=
    frontier_component_compl_closure_component_subset hVo hdich hfc hchart hξ'frZ
  have hξC : ξ ∈ C := mem_connectedComponentIn hξfrV
  have hξ'C' : ξ' ∈ C' := mem_connectedComponentIn hξ'frV
  -- `C ⊆ v`
  have hCdisj : C ∩ (u ∩ v) = ∅ :=
    Set.subset_eq_empty (Set.inter_subset_inter_left _ hC_sub) hdisj
  have hCv : C ⊆ v := by
    rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn
        u v hu hv (hC_sub.trans hsub_uv) hCdisj with h | h
    · exact absurd (h hξC) hξnu
    · exact h
  -- `C' ⊆ u`
  have hC'disj : C' ∩ (u ∩ v) = ∅ :=
    Set.subset_eq_empty (Set.inter_subset_inter_left _ hC'_sub) hdisj
  have hC'u : C' ⊆ u := by
    rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn
        u v hu hv (hC'_sub.trans hsub_uv) hC'disj with h | h
    · exact h
    · exact absurd (h hξ'C') hξ'nv
  -- `C ≠ C'`
  have hCC' : C ≠ C' := by
    intro hEq
    have hCu' : C ⊆ u := by rw [hEq]; exact hC'u
    have hmem : ξ ∈ frontier (connectedComponentIn (closure V)ᶜ x) ∩ (u ∩ v) :=
      ⟨hξfrZ, hCu' hξC, hCv hξC⟩
    rw [hdisj] at hmem; exact hmem
  -- `C ∩ C' = ∅`
  have hCC'disj : C ∩ C' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    apply hCC'
    have h1 : C = connectedComponentIn (frontier V) y := connectedComponentIn_eq hy.1
    have h2 : C' = connectedComponentIn (frontier V) y := connectedComponentIn_eq hy.2
    rw [h1, h2]
  -- the crossing phase of `C`
  obtain ⟨P⟩ := exists_crossingPhase hVo hVcl hdich hfc hchart (x₀ := ξ)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hδ : 0 < P.δ := P.δ_pos
  have hNclM : closure P.N ⊆ P.M := P.N_sub_M
  -- `ξ' ∉ closure N`
  have hξ'notclN : ξ' ∉ closure P.N := by
    intro h
    have h1 : ξ' ∈ closure P.N ∩ frontier V := ⟨h, hξ'frV⟩
    rw [P.closureN_frontier] at h1
    have h2 : ξ' ∈ C ∩ C' := ⟨h1, hξ'C'⟩
    rw [hCC'disj] at h2; exact h2
  -- crossing data at `ξ` (inside the collar `N`) and at `ξ'` (avoiding `closure N`)
  obtain ⟨z₀, v₀, η₀, S', hη₀pos, hη₀μ, hz₀Z, hv₀V, hS'G, hS'f⟩ :=
    crossing_data hVo hdich hfc hchart hξfrZ P.N_open (P.C_sub_N hξC) (half_pos hδ)
  obtain ⟨z₁, v₁, η₁, seg', hη₁pos, hη₁μ, hz₁Z, hv₁V, hseg'G, hseg'f⟩ :=
    crossing_data hVo hdich hfc hchart hξ'frZ isClosed_closure.isOpen_compl hξ'notclN one_pos
  set S := seg'.symm with hSdef
  -- the two sided lifts of `τ`
  set liftZ : X → ℝ :=
    fun y => if y ∈ P.N then 2 * Real.pi * ramp ((f y - c) / P.δ) else 0 with hliftZdef
  set liftV : X → ℝ :=
    fun y => (if y ∈ P.N then 2 * Real.pi * ramp ((f y - c) / P.δ) else 2 * Real.pi) - 2 * Real.pi
    with hliftVdef
  have hexp_sub : ∀ a : ℝ, Circle.exp (a - 2 * Real.pi) = Circle.exp a := fun a => by
    rw [sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, Circle.exp_two_pi, inv_one, mul_one]
  have hexpZ : ∀ y, Circle.exp (liftZ y) = P.τ y := by
    intro y
    simp only [hliftZdef]
    by_cases hy : y ∈ P.N
    · rw [if_pos hy, P.τ_on y hy]
    · rw [if_neg hy, Circle.exp_zero, P.τ_off y hy]
  have hexpV : ∀ y, Circle.exp (liftV y) = P.τ y := by
    intro y
    simp only [hliftVdef]
    by_cases hy : y ∈ P.N
    · rw [if_pos hy, hexp_sub, P.τ_on y hy]
    · rw [if_neg hy, hexp_sub, Circle.exp_two_pi, P.τ_off y hy]
  -- the collar-avoiding continuity domains
  set BZ : Set X := closure P.N ∩ f ⁻¹' (Set.Ici (c + P.δ / 2)) with hBZdef
  set BV : Set X := closure P.N ∩ f ⁻¹' (Set.Iic (c - P.δ / 2)) with hBVdef
  have hfcN : ContinuousOn f (closure P.N) := P.f_cont.mono hNclM
  -- continuity of `liftZ` off `BZ`
  have hliftZcont : ContinuousOn liftZ BZᶜ := by
    intro x0 hx0
    apply ContinuousAt.continuousWithinAt
    by_cases hxN : x0 ∈ P.N
    · have hxM : x0 ∈ P.M := hNclM (subset_closure hxN)
      have hfx : ContinuousAt f x0 := P.f_cont.continuousAt (P.M_open.mem_nhds hxM)
      have hform : ContinuousAt (fun y => 2 * Real.pi * ramp ((f y - c) / P.δ)) x0 := by
        have h1 : ContinuousAt (fun y => (f y - c) / P.δ) x0 :=
          (hfx.sub continuousAt_const).div_const P.δ
        exact continuousAt_const.mul (ramp_continuous.continuousAt.comp h1)
      refine hform.congr ?_
      filter_upwards [P.N_open.mem_nhds hxN] with y hy
      simp only [hliftZdef, if_pos hy]
    · by_cases hxcl : x0 ∈ closure P.N
      · have hxfrN : x0 ∈ frontier P.N := by rw [P.N_open.frontier_eq]; exact ⟨hxcl, hxN⟩
        have hgap := P.gap x0 hxfrN
        have hxM : x0 ∈ P.M := hNclM hxcl
        have hfx : ContinuousAt f x0 := P.f_cont.continuousAt (P.M_open.mem_nhds hxM)
        have hfxlt2 : f x0 < c - P.δ / 2 := by
          rcases le_or_gt c (f x0) with hge | hlt
          · exfalso
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ f x0 - c)] at hgap
            have hfle : f x0 < c + P.δ / 2 := by
              by_contra hcon
              exact hx0 ⟨hxcl, by simpa [Set.mem_preimage, Set.mem_Ici] using not_lt.mp hcon⟩
            linarith
          · rw [abs_of_neg (by linarith : f x0 - c < 0)] at hgap
            linarith
        refine (continuousAt_const (y := (0:ℝ))).congr ?_
        have hpre : f ⁻¹' (Set.Iio (c - P.δ / 2)) ∈ 𝓝 x0 :=
          hfx.preimage_mem_nhds (Iio_mem_nhds hfxlt2)
        filter_upwards [hpre] with y hy
        simp only [Set.mem_preimage, Set.mem_Iio] at hy
        simp only [hliftZdef]
        by_cases hyN : y ∈ P.N
        · rw [if_pos hyN]
          have hle : (f y - c) / P.δ ≤ -(1 / 2) := by rw [div_le_iff₀ hδ]; linarith
          rw [ramp_of_le hle, mul_zero]
        · rw [if_neg hyN]
      · refine (continuousAt_const (y := (0:ℝ))).congr ?_
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hy
        simp only [hliftZdef, if_neg (fun hyN => hy (subset_closure hyN))]
  -- continuity of `liftV` off `BV`
  have hliftVcont : ContinuousOn liftV BVᶜ := by
    intro x0 hx0
    apply ContinuousAt.continuousWithinAt
    by_cases hxN : x0 ∈ P.N
    · have hxM : x0 ∈ P.M := hNclM (subset_closure hxN)
      have hfx : ContinuousAt f x0 := P.f_cont.continuousAt (P.M_open.mem_nhds hxM)
      have hform : ContinuousAt
          (fun y => 2 * Real.pi * ramp ((f y - c) / P.δ) - 2 * Real.pi) x0 := by
        have h1 : ContinuousAt (fun y => (f y - c) / P.δ) x0 :=
          (hfx.sub continuousAt_const).div_const P.δ
        exact (continuousAt_const.mul (ramp_continuous.continuousAt.comp h1)).sub continuousAt_const
      refine hform.congr ?_
      filter_upwards [P.N_open.mem_nhds hxN] with y hy
      simp only [hliftVdef, if_pos hy]
    · by_cases hxcl : x0 ∈ closure P.N
      · have hxfrN : x0 ∈ frontier P.N := by rw [P.N_open.frontier_eq]; exact ⟨hxcl, hxN⟩
        have hgap := P.gap x0 hxfrN
        have hxM : x0 ∈ P.M := hNclM hxcl
        have hfx : ContinuousAt f x0 := P.f_cont.continuousAt (P.M_open.mem_nhds hxM)
        have hxgt : c - P.δ / 2 < f x0 := by
          by_contra hcon
          exact hx0 ⟨hxcl, by simpa [Set.mem_preimage, Set.mem_Iic] using not_lt.mp hcon⟩
        have hfxgt : c + P.δ / 2 < f x0 := by
          rcases le_or_gt (f x0) c with hle | hlt
          · exfalso
            rw [abs_of_nonpos (by linarith : f x0 - c ≤ 0)] at hgap
            linarith
          · rw [abs_of_pos (by linarith : (0:ℝ) < f x0 - c)] at hgap
            linarith
        refine (continuousAt_const (y := (0:ℝ))).congr ?_
        have hpre : f ⁻¹' (Set.Ioi (c + P.δ / 2)) ∈ 𝓝 x0 :=
          hfx.preimage_mem_nhds (Ioi_mem_nhds hfxgt)
        filter_upwards [hpre] with y hy
        simp only [Set.mem_preimage, Set.mem_Ioi] at hy
        simp only [hliftVdef]
        by_cases hyN : y ∈ P.N
        · rw [if_pos hyN]
          have hge : (1 : ℝ) / 2 ≤ (f y - c) / P.δ := by rw [le_div_iff₀ hδ]; linarith
          rw [ramp_of_ge hge, mul_one, sub_self]
        · rw [if_neg hyN, sub_self]
      · refine (continuousAt_const (y := (0:ℝ))).congr ?_
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hy
        simp only [hliftVdef, if_neg (fun hyN => hy (subset_closure hyN)), sub_self]
  -- containments of the loop pieces in the continuity domains
  have hZ_subAZ : ∀ y ∈ connectedComponentIn (closure V)ᶜ x, y ∈ BZᶜ := by
    intro y hy hyBZ
    obtain ⟨hycl, hyf⟩ := hyBZ
    have hyM : y ∈ P.M := hNclM hycl
    have hlt : c < f y := by
      simp only [Set.mem_preimage, Set.mem_Ici] at hyf; linarith
    exact (hZcompl hy) (subset_closure ((P.pos_iff y hyM).mp hlt))
  have hV_subAV : ∀ y ∈ V, y ∈ BVᶜ := by
    intro y hy hyBV
    obtain ⟨hycl, hyf⟩ := hyBV
    have hyM : y ∈ P.M := hNclM hycl
    have hlt : f y < c := by
      simp only [Set.mem_preimage, Set.mem_Iic] at hyf; linarith
    exact absurd ((P.pos_iff y hyM).mpr hy) (by linarith)
  have hcomplN_AZ : ∀ y ∉ closure P.N, y ∈ BZᶜ := fun y hy hyBZ => hy hyBZ.1
  -- `S'` avoids `BV` (its `f`-values are within `P.δ/2` of `c`)
  have hS'AV : ∀ t, S' t ∈ BVᶜ := by
    intro t hBV
    have hle : f (S' t) ≤ c - P.δ / 2 := by
      have := hBV.2; simp only [Set.mem_preimage, Set.mem_Iic] at this; exact this
    have hval : f (S' t) = c + η₀ * (1 - 2 * (t : ℝ)) := hS'f t
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hb : -η₀ ≤ η₀ * (1 - 2 * (t : ℝ)) := by nlinarith [hη₀pos, ht1]
    rw [hval] at hle
    linarith [hη₀μ]
  -- `S` avoids `closure N` entirely
  have hSmem : ∀ t, S t ∈ (closure P.N)ᶜ := by
    intro t
    have hr : (⇑S) t ∈ Set.range (⇑seg') := by
      rw [← Path.symm_range seg']; exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hr
    rw [← hs]; exact hseg'G s
  -- assemble the loop `L = (P₁ · S) · (P₂ · S')`
  set P₁ := (hZpc.joinedIn z₀ hz₀Z z₁ hz₁Z).somePath with hP₁def
  have hP₁mem : ∀ t, P₁ t ∈ connectedComponentIn (closure V)ᶜ x :=
    (hZpc.joinedIn z₀ hz₀Z z₁ hz₁Z).somePath_mem
  set P₂ := (hVpc.joinedIn v₁ hv₁V v₀ hv₀V).somePath with hP₂def
  have hP₂mem : ∀ t, P₂ t ∈ V := (hVpc.joinedIn v₁ hv₁V v₀ hv₀V).somePath_mem
  set L₁ := P₁.trans S with hL₁def
  set L₂ := P₂.trans S' with hL₂def
  set L := L₁.trans L₂ with hLdef
  have hL₁AZ : ∀ t, L₁ t ∈ BZᶜ := by
    intro t
    rw [hL₁def, Path.trans_apply]
    split
    · exact hZ_subAZ _ (hP₁mem _)
    · exact hcomplN_AZ _ (hSmem _)
  have hL₂AV : ∀ t, L₂ t ∈ BVᶜ := by
    intro t
    rw [hL₂def, Path.trans_apply]
    split
    · exact hV_subAV _ (hP₂mem _)
    · exact hS'AV _
  -- the lifted paths in `ℝ`
  have hL₁cont : Continuous (fun t => liftZ (L₁ t)) :=
    hliftZcont.comp_continuous L₁.continuous_toFun hL₁AZ
  have hL₂cont : Continuous (fun t => liftV (L₂ t)) :=
    hliftVcont.comp_continuous L₂.continuous_toFun hL₂AV
  -- junction / endpoint facts
  have hv₁notN : v₁ ∉ P.N := by
    have h0 := hseg'G 0
    rw [seg'.source] at h0
    exact fun hv => h0 (subset_closure hv)
  have hliftZ_v₁ : liftZ v₁ = 0 := by simp only [hliftZdef, if_neg hv₁notN]
  have hliftV_v₁ : liftV v₁ = 0 := by simp only [hliftVdef, if_neg hv₁notN, sub_self]
  have hz₀N : z₀ ∈ P.N := by have h1 := hS'G 1; rwa [S'.target] at h1
  have hZV : liftZ z₀ = liftV z₀ + 2 * Real.pi := by
    simp only [hliftZdef, hliftVdef, if_pos hz₀N]; ring
  set u₁ : Path (liftZ z₀) (liftZ v₁) :=
    ⟨⟨fun t => liftZ (L₁ t), hL₁cont⟩, by show liftZ (L₁ 0) = liftZ z₀; rw [L₁.source],
      by show liftZ (L₁ 1) = liftZ v₁; rw [L₁.target]⟩ with hu₁def
  set u₂ : Path (liftZ v₁) (liftV z₀) :=
    ⟨⟨fun t => liftV (L₂ t), hL₂cont⟩,
      by show liftV (L₂ 0) = liftZ v₁; rw [L₂.source, hliftV_v₁, hliftZ_v₁],
      by show liftV (L₂ 1) = liftV z₀; rw [L₂.target]⟩ with hu₂def
  set Λ : Path (liftZ z₀) (liftV z₀) := u₁.trans u₂ with hΛdef
  -- `Λ` lifts `τ ∘ L`
  have hlift : ∀ t, Circle.exp (Λ.toContinuousMap t) = P.τ (L t) := by
    intro t
    show Circle.exp (Λ t) = P.τ (L t)
    rw [hΛdef, hLdef]
    simp only [Path.trans_apply]
    split
    · exact hexpZ _
    · exact hexpV _
  -- the abstract lifting engine
  have hend := lift_endpoint_eq_of_simplyConnected P.τ.continuous L Λ.toContinuousMap hlift
  rw [show Λ.toContinuousMap 1 = liftV z₀ from Λ.target,
    show Λ.toContinuousMap 0 = liftZ z₀ from Λ.source] at hend
  rw [hZV] at hend
  linarith [hend, hπ]

end Uniformization
