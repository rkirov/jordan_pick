/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Regularity
import Uniformization.Surface.Piece.Round
import Uniformization.Surface.Fill.HoleFill
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Harmonic level-set refinement of a regular piece (W7 fallback F3, step F3.a)

Given a compact `K ∋ x₀` on a connected noncompact Riemann surface, we build an
open connected relatively compact set `V ⊇ K` whose frontier lies on a harmonic
level set `{f = c}`, together with the harmonic function `f` on an open
neighbourhood `A ⊇ frontier V`.

## Construction

1. Two regular pieces (`exists_regular_piece`): `V₁ ⊇ K` (inner) and
   `V₂ ⊇ closure V₁` (outer).
2. Cover `closure V₁` by finitely many closed chart disks `K₁ := ⋃ dᵢ.disk`
   seated inside `V₂` (`exists_disk_cover`). Set `W := V₂ \ K₁` (annular).
3. Solve the Dirichlet problem on `W` with data `1` on the inner circles and
   `0` on `frontier V₂` (`exists_dirichlet_solution`; every frontier point of
   `W` is exterior-disk regular — outer points from `V₂`, inner circle points
   from the internally tangent half-disk). This yields harmonic `h` on `W`,
   continuous on `closure W`, `[0,1]`-valued, `= 1` on the inner circles and
   `= 0` on `frontier V₂`.
4. Extend by `1` across `K₁`: `H := if x ∈ K₁ then 1 else h x`, continuous on
   the open set `V₂` (the seam continuity uses `h → 1` at the inner circles).
5. For `c ∈ (0,1)`, set `U₀ := {x ∈ V₂ | H x > c}` (open, `⊇ K`) and
   `V := fill (connectedComponentIn U₀ x₀)`. Then `frontier V ⊆ W ∩ {h = c}`:
   the frontier avoids `frontier V₂` (there `h → 0 < c`), so it is a genuine
   super-level frontier of the continuous `H` inside `V₂`.

## Delivered vs. deferred

`exists_harmonic_level_piece` delivers, sorry-free:

* the point-set piece — `V` open, connected, relatively compact, `K ⊆ V`,
  nonempty frontier, and no relatively compact complement components;
* the harmonic function `f` on the open neighbourhood `A ⊇ frontier V`
  (`A = W`, `f = H`, so `SurfaceHarmonicOn f A`);
* the level-set conjunct `∀ ξ ∈ frontier V, f ξ = c` (here `c = 1/2`).

**Deferred (cut cleanly).** Two conjuncts of the orchestrator's target are
*not* delivered here because they require the regular-value machinery, which is
substantial standalone work:

* the *nonvanishing conjugate derivative* at frontier points (conjunct (iii)):
  choosing `c` outside the countable set of critical values. The ingredients
  are available — `Rado.secondCountableTopology_of_riemannSurface`
  (`Rado.Surface.Assembly`, not yet in this import chain), the local conjugate
  `Rado.exists_conjugate`, `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`
  for the conjugate derivative, and `IsLindelof.countable` for
  discrete ⇒ countable — but assembling them (a Lindelöf cover of `W` by
  conjugate neighbourhoods, the constant/nonconstant dichotomy per piece, and
  chart-independence of the critical set) is a separate effort;
* the *sublevel relation* `A ∩ V = A ∩ {f > c}`: this fails globally (hole
  filling can add `{f < c}` lakes), and a local form near the frontier needs
  the same level-curve structure as (iii). Left to F3.b.

The `ExteriorDiskAt` conjunct is intentionally absent (F3.b derives it from the
level-curve local structure), as directed.
-/

open Set Metric Topology InnerProductSpace

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Covering a compact set by finitely many seated chart disks -/

/-- A compact set inside an open set can be covered by finitely many chart disks
whose closed carriers stay inside the open set. -/
theorem exists_disk_cover [T2Space X] {S O : Set X} (hS : IsCompact S) (hO : IsOpen O)
    (hSO : S ⊆ O) :
    ∃ disks : Finset (ChartDisk X),
      (∀ d ∈ disks, d.disk ⊆ O) ∧ S ⊆ ⋃ d ∈ disks, d.odisk := by
  classical
  -- a small seated chart disk around each point of `S`
  have hpoint : ∀ p ∈ S, ∃ d : ChartDisk X, p ∈ d.odisk ∧ d.disk ⊆ O := by
    intro p hp
    set e := chartAt ℂ p with he_def
    have hps : p ∈ e.source := mem_chart_source ℂ p
    have himg_open : IsOpen (e '' (O ∩ e.source)) :=
      e.isOpen_image_of_subset_source (hO.inter e.open_source) inter_subset_right
    have hmem : e p ∈ e '' (O ∩ e.source) := ⟨p, ⟨hSO hp, hps⟩, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg_open _ hmem
    have hseat : closedBall (e p) (ε / 2) ⊆ e.target := by
      refine ((closedBall_subset_ball (by linarith)).trans hball).trans ?_
      rintro _ ⟨x, ⟨-, hxs⟩, rfl⟩
      exact e.map_source hxs
    refine ⟨⟨e, chartAt_mem_riemannAtlas p, e p, ε / 2, by positivity, hseat⟩,
      ⟨e p, mem_ball_self (by positivity), e.left_inv hps⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have hwimg : w ∈ e '' (O ∩ e.source) :=
      hball ((closedBall_subset_ball (by linarith)) hw)
    obtain ⟨x', hx', hx'w⟩ := hwimg
    rw [← hx'w, e.left_inv hx'.2]
    exact hx'.1
  choose d hd hdO using hpoint
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover' (fun p hp => (d p hp).odisk)
    (fun p hp => (d p hp).isOpen_odisk.mem_nhds (hd p hp))
  refine ⟨t.image (fun p => d p.1 p.2), ?_, ?_⟩
  · intro dd hdd
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hdd
    exact hdO q.1 q.2
  · intro p hp
    have := ht hp
    simp only [mem_iUnion] at this
    obtain ⟨q, hq, hpq⟩ := this
    exact mem_biUnion (Finset.mem_image_of_mem _ hq) hpq

/-! ## The annular Dirichlet solution -/

/-- Distances from the endpoints of a radius to its midpoint. -/
private theorem midpt_dist {a c : ℂ} {ρ : ℝ} (h : dist a c = ρ) :
    dist a ((a + c) / 2) = ρ / 2 ∧ dist ((a + c) / 2) c = ρ / 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  refine ⟨?_, ?_⟩
  · rw [dist_eq_norm, show a - (a + c) / 2 = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]
  · rw [dist_eq_norm, show (a + c) / 2 - c = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]

set_option maxHeartbeats 1200000 in
/-- Dirichlet solution on the annular region `W = U \ K₁`, where `K₁` is a
finite union of closed chart disks seated in `U`: boundary data `1` on the inner
circles (`⊆ K₁`) and `0` on `frontier U`. -/
private theorem exists_annular_harmonic [T2Space X]
    {U : Set X} (hUo : IsOpen U) (hUc : IsCompact (closure U))
    (hfr : (frontier U).Nonempty)
    (hreg : ∀ ξ ∈ frontier U, ExteriorDiskAt U ξ)
    {disks : Finset (ChartDisk X)} (hdisk : ∀ d ∈ disks, d.disk ⊆ U) :
    ∃ h : X → ℝ,
      SurfaceHarmonicOn h (U \ ⋃ d ∈ disks, d.disk) ∧
      ContinuousOn h (closure (U \ ⋃ d ∈ disks, d.disk)) ∧
      (∀ x ∈ closure (U \ ⋃ d ∈ disks, d.disk), h x ∈ Icc (0 : ℝ) 1) ∧
      (∀ ξ ∈ frontier (U \ ⋃ d ∈ disks, d.disk),
        ξ ∈ (⋃ d ∈ disks, d.disk) → h ξ = 1) ∧
      (∀ ξ ∈ frontier U, h ξ = 0) := by
  classical
  set K₁ : Set X := ⋃ d ∈ disks, d.disk with hK₁_def
  set W : Set X := U \ K₁ with hW_def
  have hK₁cpt : IsCompact K₁ := disks.finite_toSet.isCompact_biUnion fun d _ => d.isCompact_disk
  have hK₁cl : IsClosed K₁ := hK₁cpt.isClosed
  have hK₁U : K₁ ⊆ U := by
    rw [hK₁_def]; exact iUnion₂_subset hdisk
  have hWo : IsOpen W := hUo.sdiff hK₁cl
  have hWU : W ⊆ U := sdiff_subset
  have hclW_U : closure W ⊆ closure U := closure_mono hWU
  have hclW_cpt : IsCompact (closure W) := hUc.of_isClosed_subset isClosed_closure hclW_U
  -- `interior K₁` avoids `closure W`
  have hintK₁_clW : ∀ x, x ∈ closure W → x ∉ interior K₁ := by
    have hsub : W ⊆ (interior K₁)ᶜ := fun x hx hxi => hx.2 (interior_subset hxi)
    intro x hx hxi
    exact (closure_minimal hsub isOpen_interior.isClosed_compl) hx hxi
  -- `frontier U ⊆ frontier W`
  have hfrUnotU : ∀ ξ ∈ frontier U, ξ ∉ U := by
    intro ξ hξ; rw [frontier, hUo.interior_eq] at hξ; exact hξ.2
  have hfrU_sub : frontier U ⊆ frontier W := by
    intro ξ hξ
    have hξU : ξ ∉ U := hfrUnotU ξ hξ
    have hξK₁ : ξ ∉ K₁ := fun h => hξU (hK₁U h)
    rw [hWo.frontier_eq]
    refine ⟨?_, fun h => hξU h.1⟩
    rw [_root_.mem_closure_iff]
    intro o ho hξo
    have hξclU : ξ ∈ closure U := frontier_subset_closure hξ
    have h1 : ((o ∩ K₁ᶜ) ∩ U).Nonempty :=
      _root_.mem_closure_iff.mp hξclU _ (ho.inter hK₁cl.isOpen_compl) ⟨hξo, hξK₁⟩
    obtain ⟨y, ⟨hyo, hyK₁⟩, hyU⟩ := h1
    exact ⟨y, hyo, hyU, hyK₁⟩
  have hfrW_ne : (frontier W).Nonempty := hfr.imp fun ξ hξ => hfrU_sub hξ
  -- `frontier W ⊆ frontier U ∪ innerCirc`
  have hfrW_sub : ∀ ξ ∈ frontier W,
      ξ ∈ frontier U ∨ ∃ d ∈ disks, ξ ∈ d.circ := by
    intro ξ hξ
    rw [hWo.frontier_eq] at hξ
    obtain ⟨hξcl, hξW⟩ := hξ
    have hξclU : ξ ∈ closure U := hclW_U hξcl
    by_cases hξU : ξ ∈ U
    · -- inner: on a circle
      have hξK₁ : ξ ∈ K₁ := by by_contra h; exact hξW ⟨hξU, h⟩
      have hξni : ξ ∉ interior K₁ := hintK₁_clW ξ hξcl
      simp only [hK₁_def, mem_iUnion] at hξK₁
      obtain ⟨d, hd, hξd⟩ := hξK₁
      have hodi : d.odisk ⊆ interior K₁ :=
        d.isOpen_odisk.subset_interior_iff.mpr
          (d.odisk_subset_disk.trans (subset_biUnion_of_mem hd))
      have hξod : ξ ∉ d.odisk := fun h => hξni (hodi h)
      have : ξ ∈ d.circ := by
        rcases d.disk_eq_odisk_union_circ ▸ hξd with h | h
        · exact absurd h hξod
        · exact h
      exact Or.inr ⟨d, hd, this⟩
    · exact Or.inl (by rw [frontier, hUo.interior_eq]; exact ⟨hξclU, hξU⟩)
  -- exterior disk condition at every frontier point of `W`
  have hregW : ∀ ξ ∈ frontier W, ExteriorDiskAt W ξ := by
    intro ξ hξ
    rcases hfrW_sub ξ hξ with hξU | ⟨d, hd, hξcirc⟩
    · obtain ⟨e', he', hξe', c, r, hr, hcb, hdist, hout⟩ := hreg ξ hξU
      exact ⟨e', he', hξe', c, r, hr, hcb, hdist, fun x hx => hout x ⟨hWU hx.1, hx.2⟩⟩
    · -- internally tangent half-disk at an inner circle point
      have hξs : ξ ∈ d.e.source := d.circ_subset_source hξcirc
      set a := d.e ξ with ha
      have hsphere : dist a d.c = d.ρ := (d.mem_circ_iff.mp hξcirc).2
      obtain ⟨hma, hmc⟩ := midpt_dist hsphere
      have hρ := d.ρ_pos
      refine ⟨d.e, d.he, hξs, (a + d.c) / 2, d.ρ / 2, by positivity, ?_, hma, ?_⟩
      · refine subset_trans ?_ d.seated
        intro w hw
        rw [mem_closedBall] at hw ⊢
        calc dist w d.c ≤ dist w ((a + d.c) / 2) + dist ((a + d.c) / 2) d.c := dist_triangle _ _ _
          _ ≤ d.ρ / 2 + d.ρ / 2 := add_le_add hw hmc.le
          _ = d.ρ := by ring
      · rintro x ⟨hxW, hxs⟩ hxball
        rw [mem_ball] at hxball
        have hxod : x ∈ d.odisk := by
          refine d.mem_odisk_iff.mpr ⟨hxs, ?_⟩
          rw [mem_ball]
          calc dist (d.e x) d.c ≤ dist (d.e x) ((a + d.c) / 2) + dist ((a + d.c) / 2) d.c :=
                dist_triangle _ _ _
            _ < d.ρ / 2 + d.ρ / 2 := by linarith [hmc]
            _ = d.ρ := by ring
        exact hxW.2 (mem_biUnion hd (d.odisk_subset_disk hxod))
  -- boundary data: `1` on `K₁`, `0` elsewhere
  set fbd : X → ℝ := fun x => if x ∈ K₁ then 1 else 0 with hfbd_def
  have hfbd01 : ∀ ξ ∈ frontier W, fbd ξ ∈ Icc (0 : ℝ) 1 := by
    intro ξ _; by_cases h : ξ ∈ K₁ <;> simp [hfbd_def, h]
  have hfbdc : ContinuousOn fbd (frontier W) := by
    intro ξ hξ
    by_cases hξK₁ : ξ ∈ K₁
    · have hev : ∀ᶠ y in 𝓝[frontier W] ξ, fbd y = 1 := by
        filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds (hK₁U hξK₁)), self_mem_nhdsWithin]
          with y hyU hyfr
        rcases hfrW_sub y hyfr with hyfrU | ⟨d, hd, hyd⟩
        · exact absurd hyU (hfrUnotU y hyfrU)
        · exact if_pos (mem_biUnion hd (d.circ_subset_disk hyd))
      have hfξ : fbd ξ = 1 := if_pos hξK₁
      rw [ContinuousWithinAt, hfξ]
      exact Filter.Tendsto.congr' (by filter_upwards [hev] with y hy using hy.symm) tendsto_const_nhds
    · have hev : ∀ᶠ y in 𝓝[frontier W] ξ, fbd y = 0 := by
        filter_upwards [nhdsWithin_le_nhds (hK₁cl.isOpen_compl.mem_nhds hξK₁)] with y hyK₁
        exact if_neg hyK₁
      have hfξ : fbd ξ = 0 := if_neg hξK₁
      rw [ContinuousWithinAt, hfξ]
      exact Filter.Tendsto.congr' (by filter_upwards [hev] with y hy using hy.symm) tendsto_const_nhds
  -- solve the Dirichlet problem
  obtain ⟨u, huharm, hucont, hufr, huIcc⟩ :=
    exists_dirichlet_solution hWo hclW_cpt hfrW_ne hregW hfbdc
  have hne_im : (fbd '' frontier W).Nonempty := hfrW_ne.image fbd
  have hsInf0 : (0 : ℝ) ≤ sInf (fbd '' frontier W) := by
    refine le_csInf hne_im ?_
    rintro v ⟨ξ, hξ, rfl⟩; exact (hfbd01 ξ hξ).1
  have hsSup1 : sSup (fbd '' frontier W) ≤ 1 := by
    refine csSup_le hne_im ?_
    rintro v ⟨ξ, hξ, rfl⟩; exact (hfbd01 ξ hξ).2
  refine ⟨u, huharm, hucont, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := huIcc x hx
    exact ⟨le_trans hsInf0 h1, le_trans h2 hsSup1⟩
  · intro ξ hξ hξK₁
    rw [hufr hξ]; exact if_pos hξK₁
  · intro ξ hξ
    have hξfrW : ξ ∈ frontier W := hfrU_sub hξ
    have hξK₁ : ξ ∉ K₁ := fun h => hfrUnotU ξ hξ (hK₁U h)
    rw [hufr hξfrW]; exact if_neg hξK₁

/-! ## The harmonic level-set piece -/

set_option maxHeartbeats 1200000 in
/-- **Harmonic level-set piece** (W7 fallback F3.a). Every compact `K ∋ x₀` on a
connected noncompact Riemann surface lies in an open connected relatively
compact set `V` with nonempty frontier and no relatively compact complement
components, whose frontier lies on the level set `{f = c}` of a function `f`
harmonic on an open neighbourhood `A ⊇ frontier V`.

The `ExteriorDiskAt` conjunct of the frozen target is deferred to F3.b (derived
from the level-curve local structure). -/
theorem exists_harmonic_level_piece [T2Space X] [ConnectedSpace X]
    (hnc : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ (V : Set X) (f : X → ℝ) (c : ℝ) (A : Set X),
      IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
      (frontier V).Nonempty ∧
      (∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x)) ∧
      IsOpen A ∧ frontier V ⊆ A ∧ SurfaceHarmonicOn f A ∧
      (∀ ξ ∈ frontier V, f ξ = c) := by
  classical
  have : LocallyCompactSpace X := locallyCompactSpace
  have : LocallyConnectedSpace X := locallyConnectedSpace
  -- inner regular piece `V₁ ⊇ K`
  obtain ⟨V₁, hV₁o, hV₁conn, hV₁cl, hKV₁, hx₀V₁, -, -, -⟩ := exists_regular_piece hnc hK hx₀
  set S : Set X := closure V₁ with hS_def
  have hScpt : IsCompact S := hV₁cl
  have hSconn : IsConnected S := hV₁conn.closure
  have hx₀S : x₀ ∈ S := subset_closure hx₀V₁
  have hKS : K ⊆ S := hKV₁.trans subset_closure
  -- outer regular piece `U ⊇ S`
  obtain ⟨U, hUo, hUconn, hUcl, hSU, hx₀U, hfrU, hregU, -⟩ :=
    exists_regular_piece hnc hScpt hx₀S
  -- cover `S` by chart disks seated in `U`
  obtain ⟨disks, hdiskU, hScov⟩ := exists_disk_cover hScpt hUo hSU
  set K₁ : Set X := ⋃ d ∈ disks, d.disk with hK₁_def
  set W : Set X := U \ K₁ with hW_def
  have hK₁cl : IsClosed K₁ :=
    (disks.finite_toSet.isCompact_biUnion fun d _ => d.isCompact_disk).isClosed
  have hWo : IsOpen W := hUo.sdiff hK₁cl
  have hK₁U : K₁ ⊆ U := iUnion₂_subset hdiskU
  have hSK₁ : S ⊆ K₁ := hScov.trans (iUnion₂_mono fun d _ => d.odisk_subset_disk)
  have hKK₁ : K ⊆ K₁ := hKS.trans hSK₁
  -- annular harmonic solution
  obtain ⟨h, hharm, hcont, hIcc, hinner1, hfrU0⟩ :=
    exists_annular_harmonic hUo hUcl hfrU hregU hdiskU
  -- extend by `1` across `K₁`
  set H : X → ℝ := fun x => if x ∈ K₁ then 1 else h x with hH_def
  -- `H = h` on `closure W` (they agree on the inner circles by `hinner1`)
  have hHeqh : EqOn H h (closure W) := by
    intro x hx
    by_cases hxK₁ : x ∈ K₁
    · simp only [hH_def, if_pos hxK₁]
      have hxW : x ∉ W := fun hw => hw.2 hxK₁
      have hxfrW : x ∈ frontier W := by rw [hWo.frontier_eq]; exact ⟨hx, hxW⟩
      exact (hinner1 x hxfrW hxK₁).symm
    · simp only [hH_def, if_neg hxK₁]
  -- `H` continuous on `U`
  have hHcontU : ContinuousOn H U := by
    have hHK₁eq : EqOn H (fun _ => (1 : ℝ)) K₁ := fun x hx => by simp only [hH_def, if_pos hx]
    have h1 : ContinuousOn H (closure W ∪ K₁) :=
      ContinuousOn.union_of_isClosed (hcont.congr hHeqh)
        (continuousOn_const.congr hHK₁eq) isClosed_closure hK₁cl
    refine h1.mono fun x hx => ?_
    by_cases hxK₁ : x ∈ K₁
    · exact Or.inr hxK₁
    · exact Or.inl (subset_closure ⟨hx, hxK₁⟩)
  -- the level value and the super-level set
  set c : ℝ := 1 / 2 with hc_def
  have hc0 : (0 : ℝ) < c := by norm_num [hc_def]
  have hc1 : c < 1 := by norm_num [hc_def]
  set U₀ : Set X := U ∩ {x | c < H x} with hU₀_def
  have hU₀open : IsOpen U₀ := hHcontU.isOpen_inter_preimage hUo isOpen_Ioi
  have hU₀U : U₀ ⊆ U := inter_subset_left
  have hHK₁ : ∀ x ∈ K₁, H x = 1 := fun x hx => by simp only [hH_def, if_pos hx]
  -- `S`, hence `K` and `x₀`, live in `U₀`
  have hSU₀ : S ⊆ U₀ := by
    intro x hx
    exact ⟨hSU hx, show c < H x by rw [hHK₁ x (hSK₁ hx)]; exact hc1⟩
  have hx₀U₀ : x₀ ∈ U₀ := hSU₀ hx₀S
  -- the connected component of `x₀` and its filled hull
  set cc : Set X := connectedComponentIn U₀ x₀ with hcc_def
  have hcco : IsOpen cc := hU₀open.connectedComponentIn
  have hccconn : IsConnected cc := isConnected_connectedComponentIn_iff.mpr hx₀U₀
  have hx₀cc : x₀ ∈ cc := mem_connectedComponentIn hx₀U₀
  have hccU₀ : cc ⊆ U₀ := connectedComponentIn_subset _ _
  have hSc : S ⊆ cc := hSconn.isPreconnected.subset_connectedComponentIn hx₀S hSU₀
  have hcccl : IsCompact (closure cc) :=
    hUcl.of_isClosed_subset isClosed_closure (closure_mono (hccU₀.trans hU₀U))
  set V : Set X := fill cc with hV_def
  -- frontier points of `U` are not in `closure U₀` (there `h → 0 < c`)
  have hfrUnotcl : ∀ ξ ∈ frontier U, ξ ∉ closure U₀ := by
    intro ξ hξ hcl
    have hξnU : ξ ∉ U := by rw [frontier, hUo.interior_eq] at hξ; exact hξ.2
    have hξK₁ : ξ ∉ K₁ := fun hh => hξnU (hK₁U hh)
    have hξclW : ξ ∈ closure W := by
      rw [_root_.mem_closure_iff]
      intro o ho hξo
      have hξclU : ξ ∈ closure U := frontier_subset_closure hξ
      obtain ⟨z, ⟨hzo, hzK₁⟩, hzU⟩ :=
        _root_.mem_closure_iff.mp hξclU _ (ho.inter hK₁cl.isOpen_compl) ⟨hξo, hξK₁⟩
      exact ⟨z, hzo, hzU, hzK₁⟩
    have hhξ : h ξ = 0 := hfrU0 ξ hξ
    have hcwa : Filter.Tendsto h (𝓝[closure W] ξ) (𝓝 (h ξ)) := hcont ξ hξclW
    rw [hhξ] at hcwa
    have hev : {y | h y < c} ∈ 𝓝[closure W] ξ := hcwa (Iio_mem_nhds hc0)
    obtain ⟨O, hOo, hξO, hOsub⟩ := mem_nhdsWithin.mp hev
    obtain ⟨y, ⟨hyO, hyK₁⟩, hyU₀⟩ :=
      _root_.mem_closure_iff.mp hcl (O ∩ K₁ᶜ) (hOo.inter hK₁cl.isOpen_compl) ⟨hξO, hξK₁⟩
    have hyW : y ∈ W := ⟨hyU₀.1, hyK₁⟩
    have hyHh : H y = h y := by simp only [hH_def, if_neg hyK₁]
    have hylt : h y < c := hOsub ⟨hyO, subset_closure hyW⟩
    have hlt2 : c < H y := hyU₀.2
    rw [hyHh] at hlt2
    linarith
  -- the level-set frontier bound: `frontier U₀ ⊆ W ∩ {H = c}`
  have hfrU₀ : ∀ ξ ∈ frontier U₀, ξ ∈ W ∧ H ξ = c := by
    intro ξ hξ
    have hξclU₀ : ξ ∈ closure U₀ := frontier_subset_closure hξ
    have hξnU₀ : ξ ∉ U₀ := by
      have := hξ.2; rwa [hU₀open.interior_eq] at this
    have hξclU : ξ ∈ closure U := closure_mono hU₀U hξclU₀
    have hξU : ξ ∈ U := by
      by_cases hU : ξ ∈ U
      · exact hU
      · exact absurd hξclU₀
          (hfrUnotcl ξ (by rw [frontier, hUo.interior_eq]; exact ⟨hξclU, hU⟩))
    have hnb : (𝓝[U₀] ξ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hξclU₀
    have htend : Filter.Tendsto H (𝓝[U₀] ξ) (𝓝 (H ξ)) := (hHcontU ξ hξU).mono hU₀U
    have hge : c ≤ H ξ := by
      refine ge_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin] with y hy using le_of_lt hy.2
    have hle : H ξ ≤ c := by
      by_contra hlt; exact hξnU₀ ⟨hξU, not_le.mp hlt⟩
    have hHξc : H ξ = c := le_antisymm hle hge
    have hξK₁ : ξ ∉ K₁ := by
      intro hh; rw [hHK₁ ξ hh] at hHξc; norm_num [hc_def] at hHξc
    exact ⟨⟨hξU, hξK₁⟩, hHξc⟩
  -- `frontier V ⊆ frontier U₀`
  have hfrV : frontier V ⊆ frontier U₀ :=
    (frontier_fill_subset hcco).trans (frontier_connectedComponentIn_subset hU₀open)
  -- harmonicity of `H` on `W`
  have hHW : SurfaceHarmonicOn H W := by
    intro e he z hz
    refine (harmonicAt_congr_nhds ?_).mpr (hharm e he z hz)
    filter_upwards [(isOpen_chartImage e hWo).mem_nhds hz] with w hw
    have hwW : e.symm w ∈ W := mapsTo_symm_chartImage hw
    simp only [Function.comp_apply, hH_def, if_neg hwW.2]
  -- assemble
  refine ⟨V, H, c, W, isOpen_fill hcco, isConnected_fill hnc hcco hccconn,
    isCompact_closure_fill hnc hcco hcccl, (hKS.trans hSc).trans (subset_fill cc),
    nonempty_frontier_fill hnc hcco hcccl ⟨x₀, hx₀cc⟩,
    fun x hx => not_isCompact_connectedComponentIn_compl_fill hx,
    hWo, fun ξ hξ => (hfrU₀ ξ (hfrV hξ)).1, hHW,
    fun ξ hξ => (hfrU₀ ξ (hfrV hξ)).2⟩

end Uniformization
