import Submission.Pick.Routing

/-!
# Pick's theorem: chord-end refutation and ear clipping (Module 6)

The `ChordEndUnsound` section plus the clip-simplicity (`deleteLast` ear)
development. Lives inside `namespace Pick`.
-/

namespace Pick

open LatticePolygon

variable (P : LatticePolygon)


section ChordEndUnsound

open LatticePolygon

variable (P : LatticePolygon)

end ChordEndUnsound

/-- **`ValidEarLast` reduction from an ear at the last vertex.** This packages the
two *already-discharged* ear-triangle conjuncts (3: the ear triangle is simple, 4:
it is positively oriented) — both following from `isEarVertex R ((m : ZMod R.n)+1)`
via `earTri_isSimple_of_cornerCross_ne` / `earTri_positivelyOriented_of_isEar` — and
exposes exactly the *remaining* geometric content as named hypotheses:
* `hdS` — `(deleteLast R h2).IsSimple` (conjunct 1: clipping keeps simplicity);
* `hdO` — `(deleteLast R h2).PositivelyOriented` (conjunct 2: clipping keeps CCW);
* `hdisj` — windings of the clip and the ear are never both `1` (conjunct 5: the
  diagonal separates the two interiors — the elementary/parity content);
* `hIB` — the `I,B` lattice counts add up across the diagonal (conjunct 6).
This is the single bridge from "ear at the last vertex" to `ValidEarLast`. -/
lemma validEarLast_of_ear (R : LatticePolygon) (hRS : R.IsSimple)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2)
    (hear : isEarVertex R ((m : ZMod R.n) + 1))
    (hdS : (deleteLast R h2).IsSimple)
    (hdO : (deleteLast R h2).PositivelyOriented)
    (hdisj : ∀ q, q ∉ R.boundary →
      ¬((deleteLast R h2).winding q = 1 ∧ (earTri R m hm).winding q = 1))
    (hIB : (R.I : ℝ) + (R.B : ℝ) / 2 = ((deleteLast R h2).I : ℝ) + ((earTri R m hm).I : ℝ)
      + (((deleteLast R h2).B : ℝ) + ((earTri R m hm).B : ℝ)) / 2 - 1) :
    ValidEarLast R := by
  refine ⟨h2, m, hm, hdS, hdO,
    earTri_isSimple_of_cornerCross_ne R m hm (ne_of_gt hear.1),
    earTri_positivelyOriented_of_isEar R m hm hear, ?_, hIB⟩
  -- off-boundary disjointness ⟹ a.e. disjointness (boundary is Lebesgue-null)
  have hbnull : R.boundaryᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff, compl_compl]; exact volume_boundary_eq_zero R hRS
  filter_upwards [hbnull] with q hqb using hdisj q hqb

/-- **`ValidEarLast` from an ear at the last vertex (bundled form).** Specialization
of `validEarLast_of_ear` where the four remaining geometric facts are bundled as a
single existential over `(h2, m, hm)`. The ear-triangle conjuncts (3,4) are
discharged from `isEarVertex` at the last vertex `(m : ZMod R.n) + 1`. -/
lemma validEarLast_of_earLast (R : LatticePolygon) (hRS : R.IsSimple)
    (hex : ∃ (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2),
      isEarVertex R ((m : ZMod R.n) + 1) ∧
      (deleteLast R h2).IsSimple ∧ (deleteLast R h2).PositivelyOriented ∧
      (∀ q, q ∉ R.boundary →
        ¬((deleteLast R h2).winding q = 1 ∧ (earTri R m hm).winding q = 1)) ∧
      ((R.I : ℝ) + (R.B : ℝ) / 2 = ((deleteLast R h2).I : ℝ) + ((earTri R m hm).I : ℝ)
        + (((deleteLast R h2).B : ℝ) + ((earTri R m hm).B : ℝ)) / 2 - 1)) :
    ValidEarLast R := by
  obtain ⟨h2, m, hm, hear, hdS, hdO, hdisj, hIB⟩ := hex
  exact validEarLast_of_ear R hRS h2 m hm hear hdS hdO hdisj hIB

/-- **The remaining geometric content of Pick's theorem, as one hypothesis.**
`EarExistence` asserts that every simple positively-oriented polygon with `≥ 4`
vertices can be rotated so that its *last* vertex is an ear whose clip
(`deleteLast`) is again simple and positively oriented, with disjoint windings and
additive `I,B` counts. This is exactly `EarProvider` with the (already-proved)
ear-triangle simplicity/orientation conjuncts removed — i.e. the genuine remaining
work (convex-vertex existence + clip-simplicity + clip-orientation + winding
disjointness + `I,B` additivity). -/
def EarExistence : Prop :=
  ∀ Q : LatticePolygon, Q.IsSimple → Q.PositivelyOriented → 4 ≤ Q.n →
    ∃ c : ZMod Q.n, ∃ (h2 : 2 ≤ (rotateP Q c).n) (m : ℕ) (hm : (rotateP Q c).n = m + 2),
      isEarVertex (rotateP Q c) ((m : ZMod (rotateP Q c).n) + 1) ∧
      (deleteLast (rotateP Q c) h2).IsSimple ∧
      (deleteLast (rotateP Q c) h2).PositivelyOriented ∧
      (∀ q, q ∉ (rotateP Q c).boundary →
        ¬((deleteLast (rotateP Q c) h2).winding q = 1 ∧
        (earTri (rotateP Q c) m hm).winding q = 1)) ∧
      (((rotateP Q c).I : ℝ) + ((rotateP Q c).B : ℝ) / 2
        = ((deleteLast (rotateP Q c) h2).I : ℝ) + ((earTri (rotateP Q c) m hm).I : ℝ)
          + (((deleteLast (rotateP Q c) h2).B : ℝ)
            + ((earTri (rotateP Q c) m hm).B : ℝ)) / 2 - 1)

/-- **`EarExistence → EarProvider`.** The ear-triangle conjuncts (3,4) of
`ValidEarLast` are discharged from `isEarVertex`, so an ear at the last vertex (with
its clip simple+oriented, disjoint windings, additive counts) yields a valid
ear-clipping split. Hence Pick's theorem reduces to `EarExistence`. -/
lemma earProvider_of_earExistence (hee : EarExistence) : EarProvider := by
  intro Q hS hO hn
  obtain ⟨c, h2, m, hm, hear, hdS, hdO, hdisj, hIB⟩ := hee Q hS hO hn
  exact ⟨c, validEarLast_of_earLast (rotateP Q c) (isSimple_rotateP Q c hS)
    ⟨h2, m, hm, hear, hdS, hdO, hdisj, hIB⟩⟩

/-- **Pick's theorem, reduced to `EarExistence`.** Combining
`earProvider_of_earExistence` with `pick_of_provider`: every simple
positively-oriented lattice polygon has area `I + B/2 − 1`, *given* `EarExistence`
(the remaining geometric input). -/
theorem pick_of_earExistence (hee : EarExistence) (P : LatticePolygon)
    (hsimple : P.IsSimple) (horient : P.PositivelyOriented) :
    P.area = (P.I : ℝ) + (P.B : ℝ) / 2 - 1 :=
  pick_of_provider (earProvider_of_earExistence hee) P hsimple horient

/-! ### Clip simplicity: `deleteLast` of an ear is simple

The clipped polygon `deleteLast R` replaces the two edges through the apex `v_{m+1}`
by the single diagonal `v_m → v_0`. We first record how `deleteLast`'s edges
reindex onto `R`'s edges (a "kept" edge for `j.val < m`, the new diagonal for
`j.val = m`), then verify each `IsSimple` clause. -/

/-- A **kept edge** of the clip: for `j.val < m`, edge `j` of `deleteLast R`
coincides with edge `↑j.val` of `R`. -/
lemma deleteLast_edgeSeg_kept (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) (j : ZMod (deleteLast R h2).n) (hj : j.val < m) :
    (deleteLast R h2).edgeSeg j = R.edgeSeg ((j.val : ℕ) : ZMod R.n) := by
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  have hcast : (j + 1) = ((j.val + 1 : ℕ) : ZMod (deleteLast R h2).n) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have hsucc : ((j + 1).val : ℕ) = j.val + 1 := by
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hidx : ((((j + 1).val) : ℕ) : ZMod R.n) = ((j.val : ℕ) : ZMod R.n) + 1 := by
    rw [hsucc]; push_cast; ring
  rw [LatticePolygon.edgeSeg, LatticePolygon.edgeSeg, deleteLast_vert, deleteLast_vert]
  congr 2
  exact congrArg R.vert hidx

/-- The **diagonal edge** of the clip: the last edge `j.val = m` of `deleteLast R`
is the diagonal segment `v_m → v_0`. -/
lemma deleteLast_edgeSeg_diag (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) (j : ZMod (deleteLast R h2).n) (hj : j.val = m) :
    (deleteLast R h2).edgeSeg j
      = segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) := by
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  have hcast : (j + 1) = ((j.val + 1 : ℕ) : ZMod (deleteLast R h2).n) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have hz : (j + 1) = 0 := by
    rw [hcast, hj, hn1]; exact_mod_cast ZMod.natCast_self (m + 1)
  have hzval : ((j + 1).val : ℕ) = 0 := by rw [hz, ZMod.val_zero]
  have hidxA : ((j.val : ℕ) : ZMod R.n) = (m : ZMod R.n) := by rw [hj]
  have hidxB : ((((j + 1).val) : ℕ) : ZMod R.n) = (0 : ZMod R.n) := by rw [hzval]; simp
  rw [LatticePolygon.edgeSeg, deleteLast_vert, deleteLast_vert]
  congr 2
  · exact congrArg R.vert hidxA
  · exact congrArg R.vert hidxB

/-- Every clip index `j` is either a kept edge (`j.val < m`) or the diagonal
(`j.val = m`). -/
lemma deleteLast_idx_dichotomy (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) (j : ZMod (deleteLast R h2).n) : j.val < m ∨ j.val = m := by
  have hlt := ZMod.val_lt j
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  omega

/-- The R-index of a kept edge's successor: `↑(j+1).val = ↑j.val + 1` in `ZMod R.n`. -/
lemma deleteLast_idx_succ (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) (j : ZMod (deleteLast R h2).n) (hj : j.val < m) :
    ((((j + 1).val) : ℕ) : ZMod R.n) = ((j.val : ℕ) : ZMod R.n) + 1 := by
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  have hcast : (j + 1) = ((j.val + 1 : ℕ) : ZMod (deleteLast R h2).n) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have hsucc : ((j + 1).val : ℕ) = j.val + 1 := by
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [hsucc]; push_cast; ring

/-- The diagonal clip index `↑m` is the last index, so `↑m + 1 = 0` in `ZMod (R.n-1)`. -/
lemma deleteLast_last_succ (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) :
    ((m : ℕ) : ZMod (deleteLast R h2).n) + 1 = 0 := by
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  rw [← Nat.cast_one (R := ZMod (deleteLast R h2).n), ← Nat.cast_add,
    show m + 1 = (deleteLast R h2).n from hn1.symm, ZMod.natCast_self]

/-- The R-index map `j ↦ ↑j.val : ZMod (R.n-1) → ZMod R.n` is injective (both
vals are `< R.n - 1 ≤ R.n`). -/
lemma deleteLast_idx_inj (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) (i j : ZMod (deleteLast R h2).n)
    (he : ((i.val : ℕ) : ZMod R.n) = ((j.val : ℕ) : ZMod R.n)) : i = j := by
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
  exact ZMod.val_injective _ he

/-- **Conjunct 1 for the clip: no degenerate edge.** Each edge of `deleteLast R`
is nondegenerate: kept edges inherit `R`'s nondegeneracy; the diagonal `v_m → v_0`
is nondegenerate because `v_m ≠ v_0` (distinct vertices of the simple polygon). -/
lemma deleteLast_nondegenerate_of_ear (R : LatticePolygon) (hS : R.IsSimple)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm1 : 1 ≤ m) :
    ∀ i, (deleteLast R h2).vert i ≠ (deleteLast R h2).vert (i + 1) := by
  intro i
  have hmne0 : (m : ZMod R.n) ≠ 0 := by
    intro he
    have hv : ((m : ZMod R.n)).val = m := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [he] at hv; simp at hv; omega
  have hdiagNd : R.vert (m : ZMod R.n) ≠ R.vert 0 := fun he => hmne0 (vert_injective R hS he)
  rcases deleteLast_idx_dichotomy R h2 m hm i with hlt | heq
  · -- kept edge
    rw [deleteLast_vert, deleteLast_vert]
    intro he
    have hidx : ((((i + 1).val) : ℕ) : ZMod R.n) = ((i.val : ℕ) : ZMod R.n) + 1 :=
      deleteLast_idx_succ R h2 m hm i hlt
    apply hS.1 ((i.val : ℕ) : ZMod R.n)
    rw [← hidx]; exact he
  · -- diagonal edge
    have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
    have hcast : (i + 1) = ((i.val + 1 : ℕ) : ZMod (deleteLast R h2).n) := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    have hz : (i + 1) = 0 := by
      rw [hcast, heq, hn1]; exact_mod_cast ZMod.natCast_self (m + 1)
    have hzval : ((i + 1).val : ℕ) = 0 := by rw [hz, ZMod.val_zero]
    have hidxA : ((i.val : ℕ) : ZMod R.n) = (m : ZMod R.n) := by rw [heq]
    have hidxB : ((((i + 1).val) : ℕ) : ZMod R.n) = (0 : ZMod R.n) := by rw [hzval]; simp
    rw [deleteLast_vert, deleteLast_vert]
    intro he
    apply hdiagNd
    rw [← hidxA, ← hidxB]
    exact he

/-- **Clause 2 for the clip, kept–kept case.** Two distinct, non-adjacent kept
edges of `deleteLast R` are disjoint, inherited from `R`'s simplicity. -/
lemma deleteLast_kept_disjoint (R : LatticePolygon) (hS : R.IsSimple) (h2 : 2 ≤ R.n)
    (m : ℕ) (hm : R.n = m + 2) (i j : ZMod (deleteLast R h2).n)
    (hi : i.val < m) (hj : j.val < m)
    (hne : i ≠ j) (hadj1 : i + 1 ≠ j) (hadj2 : j + 1 ≠ i) :
    Disjoint (R.edgeSeg ((i.val : ℕ) : ZMod R.n)) (R.edgeSeg ((j.val : ℕ) : ZMod R.n)) := by
  apply hS.2.1
  · intro he; exact hne (deleteLast_idx_inj R h2 m hm i j he)
  · rw [← deleteLast_idx_succ R h2 m hm i hi]
    intro he; exact hadj1 (deleteLast_idx_inj R h2 m hm (i + 1) j he)
  · rw [← deleteLast_idx_succ R h2 m hm j hj]
    intro he; exact hadj2 (deleteLast_idx_inj R h2 m hm (j + 1) i he)

/-- The kept R-edge index `↑i.val` lands in `{1,…,m}`-complement of the diagonal
endpoints exactly when `i` is a non-diagonal-adjacent clip index. Packaged: from the
clip non-adjacency `i+1 ≠ last` and `i ≠ 0` (and `i.val < m`), the R-edge index
`↑i.val` avoids `m-1`, `m`, and `0`. -/
lemma deleteLast_kept_idx_avoid (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2)
    (hm1 : 1 ≤ m) (i : ZMod (deleteLast R h2).n) (hi : i.val < m)
    (h0 : i ≠ 0) (hlast : i ≠ ((m : ℕ) - 1 : ℕ)) :
    ((i.val : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) - 1 ∧
    ((i.val : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) ∧
    ((i.val : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) + 1 ∧
    ((i.val : ℕ) : ZMod R.n) ≠ 0 := by
  have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
  -- i.val as a nat
  have hival : ((((i.val : ℕ)) : ZMod R.n)).val = i.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ≠ m - 1
    have hmm1 : ((m : ZMod R.n) - 1) = (((m - 1 : ℕ)) : ZMod R.n) := by
      rw [Nat.cast_sub hm1]; push_cast; ring
    rw [hmm1]
    intro he
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    exact hlast (by rw [← ZMod.natCast_zmod_val i, he])
  · intro he
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at he
    omega
  · -- ≠ m + 1
    have hmp1 : ((m : ZMod R.n) + 1) = (((m + 1 : ℕ)) : ZMod R.n) := by push_cast; ring
    rw [hmp1]
    intro he
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at he
    omega
  · intro he
    apply h0
    have hz : i.val = 0 := by
      have : ((i.val : ℕ) : ZMod R.n).val = (0 : ZMod R.n).val := by rw [he]
      rwa [hival, ZMod.val_zero] at this
    rw [← ZMod.natCast_zmod_val i, hz, Nat.cast_zero]

/-- **The clip's diagonal R-edge `↑(m-1)` is the segment `v_{m-1} → v_m`.** -/
lemma deleteLast_edge_pre_diag (R : LatticePolygon) (m : ℕ) (_hm : R.n = m + 2) (hm1 : 1 ≤ m) :
    R.edgeSeg (((m - 1 : ℕ)) : ZMod R.n)
      = segment ℝ (toReal (R.vert (((m - 1 : ℕ)) : ZMod R.n))) (toReal (R.vert (m : ZMod R.n))) := by
  rw [LatticePolygon.edgeSeg]
  congr 2
  rw [Nat.cast_sub hm1]; push_cast; ring_nf

/-- **The clip's R-edge `0` is the segment `v_0 → v_1`.** -/
lemma deleteLast_edge_zero (R : LatticePolygon) (m : ℕ) (_hm : R.n = m + 2) :
    R.edgeSeg (0 : ZMod R.n)
      = segment ℝ (toReal (R.vert 0)) (toReal (R.vert 1)) := by
  rw [LatticePolygon.edgeSeg]; norm_num

/-- **`deleteLast` of an ear is simple.** The clip of a simple polygon `R` (with
`R.n = m + 2`, `m ≥ 1`) at its last vertex is again simple, provided the new
diagonal `v_m → v_0` is geometrically well-behaved: it makes a genuine turn with
each incident edge (`hAdjPrev`, `hAdjNext`, ruling out collinear backtracking at the
shared vertices `v_m`, `v_0`) and is disjoint from every non-incident edge of `R`
(`hDisj`, the empty-ear/diagonal-non-crossing content). Conjunct 1 (nondegeneracy)
is discharged unconditionally from `R`'s simplicity; conjunct 2 splits into the
kept–kept case (from `R`) and the diagonal–kept case (`hDisj`); conjunct 3 splits
into the kept–kept case (from `R`) and the two diagonal-adjacency cases
(`hAdjPrev`, `hAdjNext`). -/
lemma deleteLast_isSimple_of_ear (R : LatticePolygon) (hS : R.IsSimple)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm1 : 1 ≤ m)
    (hAdjPrev : segment ℝ (toReal (R.vert (((m - 1 : ℕ)) : ZMod R.n))) (toReal (R.vert (m : ZMod R.n)))
                  ∩ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
                = {toReal (R.vert (m : ZMod R.n))})
    (hAdjNext : segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
                  ∩ segment ℝ (toReal (R.vert 0)) (toReal (R.vert 1))
                = {toReal (R.vert 0)})
    (hDisj : ∀ k : ZMod R.n, k ≠ (m : ZMod R.n) - 1 → k ≠ (m : ZMod R.n) →
        k ≠ (m : ZMod R.n) + 1 → k ≠ 0 →
        Disjoint (segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))) (R.edgeSeg k)) :
    (deleteLast R h2).IsSimple := by
  refine ⟨deleteLast_nondegenerate_of_ear R hS h2 m hm hm1, ?_, ?_⟩
  · -- Clause 2: non-adjacent edges disjoint
    intro i j hne hadj1 hadj2
    rcases deleteLast_idx_dichotomy R h2 m hm i with hi | hi <;>
      rcases deleteLast_idx_dichotomy R h2 m hm j with hj | hj
    · -- both kept
      rw [deleteLast_edgeSeg_kept R h2 m hm i hi, deleteLast_edgeSeg_kept R h2 m hm j hj]
      exact deleteLast_kept_disjoint R hS h2 m hm i j hi hj hne hadj1 hadj2
    · -- i kept, j diagonal
      rw [deleteLast_edgeSeg_kept R h2 m hm i hi, deleteLast_edgeSeg_diag R h2 m hm j hj]
      refine Disjoint.symm ?_
      -- i avoids the diagonal's R-neighbours
      have h0 : i ≠ 0 := by
        rintro rfl
        apply hadj2
        have hjlast : j = ((m : ℕ) : ZMod (deleteLast R h2).n) := by
          rw [← ZMod.natCast_zmod_val j, hj]
        rw [hjlast]; exact deleteLast_last_succ R h2 m hm
      have hlast : i ≠ ((m : ℕ) - 1 : ℕ) := by
        rintro rfl
        apply hadj1
        have hjval : j = ((m : ℕ) : ZMod (deleteLast R h2).n) := by
          rw [← ZMod.natCast_zmod_val j, hj]
        rw [hjval, ← Nat.cast_one (R := ZMod (deleteLast R h2).n), ← Nat.cast_add,
          show m - 1 + 1 = m by omega]
      obtain ⟨ha, hb, hbp1, hc⟩ := deleteLast_kept_idx_avoid R h2 m hm hm1 i hi h0 hlast
      exact hDisj _ ha hb hbp1 hc
    · -- i diagonal, j kept
      rw [deleteLast_edgeSeg_diag R h2 m hm i hi, deleteLast_edgeSeg_kept R h2 m hm j hj]
      have h0 : j ≠ 0 := by
        rintro rfl
        apply hadj1
        have hilast : i = ((m : ℕ) : ZMod (deleteLast R h2).n) := by
          rw [← ZMod.natCast_zmod_val i, hi]
        rw [hilast]; exact deleteLast_last_succ R h2 m hm
      have hlast : j ≠ ((m : ℕ) - 1 : ℕ) := by
        rintro rfl
        apply hadj2
        have hival2 : i = ((m : ℕ) : ZMod (deleteLast R h2).n) := by
          rw [← ZMod.natCast_zmod_val i, hi]
        rw [hival2, ← Nat.cast_one (R := ZMod (deleteLast R h2).n), ← Nat.cast_add,
          show m - 1 + 1 = m by omega]
      obtain ⟨ha, hb, hbp1, hc⟩ := deleteLast_kept_idx_avoid R h2 m hm hm1 j hj h0 hlast
      exact hDisj _ ha hb hbp1 hc
    · -- both diagonal: impossible (same index)
      exact absurd (deleteLast_idx_inj R h2 m hm i j (by rw [hi, hj])) hne
  · -- Clause 3: adjacent edges meet exactly at the shared vertex
    intro i
    have hn1 : (deleteLast R h2).n = m + 1 := by rw [deleteLast_n]; omega
    -- the shared vertex `D.vert (i+1)`
    rcases (show i.val < m - 1 ∨ i.val = m - 1 ∨ i.val = m from by
      have hvl := ZMod.val_lt i; omega) with hlt | hmid | hlast
    · -- both `i` and `i+1` kept
      have hi : i.val < m := by omega
      have hsucc : ((i + 1).val : ℕ) = i.val + 1 := by
        have hcast : (i + 1) = ((i.val + 1 : ℕ) : ZMod (deleteLast R h2).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have hi1 : (i + 1).val < m := by rw [hsucc]; omega
      have hes1 : (deleteLast R h2).edgeSeg i = R.edgeSeg ((i.val : ℕ) : ZMod R.n) :=
        deleteLast_edgeSeg_kept R h2 m hm i hi
      have hes2 : (deleteLast R h2).edgeSeg (i + 1) = R.edgeSeg (((i.val : ℕ) : ZMod R.n) + 1) := by
        rw [deleteLast_edgeSeg_kept R h2 m hm (i + 1) hi1, deleteLast_idx_succ R h2 m hm i hi]
      have hdv : (deleteLast R h2).vert (i + 1) = R.vert (((i.val : ℕ) : ZMod R.n) + 1) := by
        rw [deleteLast_vert]; exact congrArg R.vert (deleteLast_idx_succ R h2 m hm i hi)
      rw [hes1, hes2, hdv]
      exact hS.2.2 ((i.val : ℕ) : ZMod R.n)
    · -- `i` kept (val = m-1), `i+1` is the diagonal (val = m)
      have hi : i.val < m := by omega
      have hsucc : ((i + 1).val : ℕ) = m := by
        have hcast : (i + 1) = ((i.val + 1 : ℕ) : ZMod (deleteLast R h2).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, ZMod.val_natCast, hmid, Nat.mod_eq_of_lt (by omega)]; omega
      have hes1 : (deleteLast R h2).edgeSeg i
          = segment ℝ (toReal (R.vert (((m - 1 : ℕ)) : ZMod R.n))) (toReal (R.vert (m : ZMod R.n))) := by
        rw [deleteLast_edgeSeg_kept R h2 m hm i hi,
          show ((i.val : ℕ) : ZMod R.n) = (((m - 1 : ℕ)) : ZMod R.n) by rw [hmid],
          deleteLast_edge_pre_diag R m hm hm1]
      have hes2 : (deleteLast R h2).edgeSeg (i + 1)
          = segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) :=
        deleteLast_edgeSeg_diag R h2 m hm (i + 1) hsucc
      have hdv : (deleteLast R h2).vert (i + 1) = R.vert (m : ZMod R.n) := by
        rw [deleteLast_vert]
        exact congrArg R.vert (show ((((i + 1).val : ℕ)) : ZMod R.n) = ((m : ℕ) : ZMod R.n) by rw [hsucc])
      rw [hes1, hes2, hdv]
      exact hAdjPrev
    · -- `i` is the diagonal (val = m), `i+1` is edge `0`
      have hz : (i + 1) = 0 := by
        have hcast : (i + 1) = ((i.val + 1 : ℕ) : ZMod (deleteLast R h2).n) := by
          rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        rw [hcast, hlast, hn1]; exact_mod_cast ZMod.natCast_self (m + 1)
      have hzval : ((i + 1).val : ℕ) = 0 := by rw [hz, ZMod.val_zero]
      have hi1 : (i + 1).val < m := by rw [hzval]; omega
      have hk0 : ((((i + 1).val : ℕ)) : ZMod R.n) = (0 : ZMod R.n) := by rw [hzval]; simp
      have hes1 : (deleteLast R h2).edgeSeg i
          = segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0)) :=
        deleteLast_edgeSeg_diag R h2 m hm i hlast
      have hes2 : (deleteLast R h2).edgeSeg (i + 1)
          = segment ℝ (toReal (R.vert 0)) (toReal (R.vert 1)) := by
        rw [deleteLast_edgeSeg_kept R h2 m hm (i + 1) hi1, hk0, deleteLast_edge_zero R m hm]
      have hdv : (deleteLast R h2).vert (i + 1) = R.vert 0 := by
        rw [deleteLast_vert]; exact congrArg R.vert hk0
      rw [hes1, hes2, hdv]
      exact hAdjNext

/-- **Clip-orientation reduction (conjunct 2).** Given `R` positively oriented, the
clipped polygon `deleteLast R` is positively oriented **iff** the clipped ear's
signed area is strictly less than `R`'s. This isolates the entire remaining content
of `ValidEarLast`'s conjunct 2 into the single signed-area comparison
`earTri.shoelace < R.shoelace`: the ear (a positive-area triangle) does not consume
all of `R`'s area. Pure algebra from `shoelace_eq_deleteLast_add_earTri`. -/
lemma deleteLast_positivelyOriented_iff (R : LatticePolygon) (h2 : 2 ≤ R.n) (m : ℕ)
    (hm : R.n = m + 2) :
    (deleteLast R h2).PositivelyOriented ↔ (earTri R m hm).shoelace < R.shoelace := by
  have hadd := shoelace_eq_deleteLast_add_earTri R h2 m hm
  unfold LatticePolygon.PositivelyOriented
  constructor <;> intro h <;> linarith

/-! ### Empty-ear diagonal validity: the two turn intersections (`hAdjPrev`, `hAdjNext`)

For an **empty ear** at apex `i = m+1` (triangle `(vₘ, vₘ₊₁, v₀)` containing no other
vertex), the diagonal `D = [vₘ, v₀]` meets each *incident* edge only at the shared
vertex. Unlike a bare non-collinearity (`cross ≠ 0`, which can genuinely fail at a flat
straight-through vertex), the correct statement is the segment intersection equality,
discharged by `segment_inter_eq_endpoint_of_not_sameRay`: the only excluded configuration
is the two segments overlapping along a common ray, which the empty-ear property
(`vⱼ ∉ closed T`) and `R`'s simplicity both forbid. -/

/-- The diagonal `[vₘ, v₀]` lies in the closed ear triangle `(vₘ, vₘ₊₁, v₀)`: it is the
base edge `[a, c]` of the positively-oriented (`0 < cornerCross R (m+1)`) triangle. -/
lemma earTri_cross_base_pos (R : LatticePolygon) (m : ℕ) (hm : R.n = m + 2)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    0 < cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
              (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n))) := by
  have h2 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  have h1 : ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) := by ring
  rw [show cross (toReal (R.vert ((m : ZMod R.n) + 1)) - toReal (R.vert (m : ZMod R.n)))
        (toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n)))
      = cornerCross R ((m : ZMod R.n) + 1) by
    unfold cornerCross; rw [h1, h2]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring]
  exact hear.1

/-- Membership helper: `y = (1-t)•x + t•z` puts `y` on `segment ℝ x z`. -/
private lemma seg_of_affine {x y z : ℝ × ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hy : y = (1 - t) • x + t • z) : y ∈ segment ℝ x z :=
  ⟨1 - t, t, by linarith, ht0, by ring, by rw [hy]⟩

/-- **`hAdjNext` for an empty ear.** The diagonal `[vₘ, v₀]` and the outgoing edge
`[v₀, v₁]` meet exactly at the shared vertex `v₀`. If they overlapped along a common
ray from `v₀`, then either `v₁ ∈ [vₘ, v₀] ⊆ closed ear-triangle` (contradicting the
empty-ear hypothesis at the vertex `v₁`) or `vₘ ∈ [v₀, v₁] = edge 0` while
`vₘ ∈ edge m` (contradicting `R`'s simplicity, edges `0` and `m` being non-adjacent). -/
lemma diag_adjNext_inter (R : LatticePolygon) (hS : R.IsSimple) (m : ℕ) (hm : R.n = m + 2)
    (hm2 : 2 ≤ m) (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
      ∩ segment ℝ (toReal (R.vert 0)) (toReal (R.vert 1))
    = {toReal (R.vert 0)} := by
  classical
  have hbase := earTri_cross_base_pos R m hm hear
  -- index facts
  have hn : (R.n : ℕ) = m + 2 := hm
  have hmne0 : (m : ZMod R.n) ≠ 0 := by
    intro he
    have : ((m : ZMod R.n)).val = (0 : ZMod R.n).val := by rw [he]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at this; omega
  have h1ne0 : (1 : ZMod R.n) ≠ 0 := by
    have : (1 : ZMod R.n).val = 1 := by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    intro he; rw [he, ZMod.val_zero] at this; omega
  have h1nem : (1 : ZMod R.n) ≠ (m : ZMod R.n) := by
    intro he
    have hv1 : (1 : ZMod R.n).val = 1 := by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    have hvm : ((m : ZMod R.n)).val = m := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have : (1 : ZMod R.n).val = ((m : ZMod R.n)).val := by rw [he]
    rw [hv1, hvm] at this; omega
  have h1nemp1 : (1 : ZMod R.n) ≠ (m : ZMod R.n) + 1 := by
    intro he
    apply hmne0
    have : (m : ZMod R.n) = 0 := by linear_combination -he
    exact this
  -- vertices distinct
  have hvm0 : R.vert (m : ZMod R.n) ≠ R.vert 0 := fun he => hmne0 (vert_injective R hS he)
  have hv01 : R.vert 0 ≠ R.vert 1 := by
    have := hS.1 0; rwa [zero_add] at this
  rw [segment_symm ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))]
  apply segment_inter_eq_endpoint_of_not_sameRay
  intro hsr
  have hne1 : toReal (R.vert (m : ZMod R.n)) - toReal (R.vert 0) ≠ 0 := by
    rw [sub_ne_zero]; exact fun he => hvm0 (toReal_injective he)
  have hne2 : toReal (R.vert 1) - toReal (R.vert 0) ≠ 0 := by
    rw [sub_ne_zero]; exact fun he => hv01 (toReal_injective he).symm
  obtain ⟨r, hr0, hreq⟩ := hsr.exists_pos_left hne1 hne2
  set a := toReal (R.vert (m : ZMod R.n)) with ha
  set c := toReal (R.vert 0) with hc
  set d := toReal (R.vert 1) with hd
  rcases le_total r 1 with hr1 | hr1
  · -- v₁ ∈ [v₀, vₘ] ⊆ closed ear triangle → empty-ear contradiction
    have hmem : d ∈ segment ℝ c a := by
      apply seg_of_affine hr0.le hr1
      have hh : d - c = r • (a - c) := hreq.symm
      rw [smul_sub] at hh
      have : d = (1 - r) • c + r • a := by
        have hd2 : d = c + (r • a - r • c) := by rw [← hh]; abel
        rw [hd2, sub_smul, one_smul]; abel
      exact this
    have hin : inTriangle a (toReal (R.vert ((m : ZMod R.n) + 1))) c d :=
      inTriangle_of_mem_segment_fst_thd a (toReal (R.vert ((m : ZMod R.n) + 1))) c d
        hbase.le (by rw [segment_symm]; exact hmem)
    exact hear.2 1 (by
        show (1 : ZMod R.n) ≠ ((m : ZMod R.n) + 1) - 1
        rw [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring]; exact h1nem)
      (by show (1 : ZMod R.n) ≠ (m : ZMod R.n) + 1; exact h1nemp1)
      (by show (1 : ZMod R.n) ≠ (m : ZMod R.n) + 1 + 1
          rw [show ((m : ZMod R.n) + 1 + 1) = (0 : ZMod R.n) by
            have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
            push_cast at hz; linear_combination hz]
          exact h1ne0)
      (by show inTriangle (toReal (R.vert ((m : ZMod R.n) + 1 - 1)))
            (toReal (R.vert ((m : ZMod R.n) + 1)))
            (toReal (R.vert ((m : ZMod R.n) + 1 + 1))) (toReal (R.vert 1))
          rw [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring,
            show ((m : ZMod R.n) + 1 + 1) = (0 : ZMod R.n) by
              have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
              push_cast at hz; linear_combination hz]
          exact hin)
  · -- vₘ ∈ [v₀, v₁] = edge 0, and vₘ ∈ edge m ; edges 0,m non-adjacent → disjoint, contra
    have hrpos : (0:ℝ) < r := hr0
    have hsinv : (0:ℝ) ≤ 1 / r := by positivity
    have hsinv1 : 1 / r ≤ 1 := by rw [div_le_one hrpos]; exact hr1
    have hmem : a ∈ segment ℝ c d := by
      apply seg_of_affine hsinv hsinv1
      have hac : a - c = (1 / r) • (d - c) := by
        have hh : d - c = r • (a - c) := hreq.symm
        rw [hh, smul_smul, one_div, inv_mul_cancel₀ hr0.ne', one_smul]
      rw [smul_sub] at hac
      have : a = (1 - 1 / r) • c + (1 / r) • d := by
        have ha2 : a = c + ((1/r) • d - (1/r) • c) := by rw [← hac]; abel
        rw [ha2, sub_smul, one_smul]; abel
      exact this
    have hmemE0 : a ∈ R.edgeSeg 0 := by
      rw [LatticePolygon.edgeSeg]
      have : (0 : ZMod R.n) + 1 = 1 := by ring
      rw [this, ← hc, ← hd]; exact hmem
    have hmemEm : a ∈ R.edgeSeg (m : ZMod R.n) := by
      rw [LatticePolygon.edgeSeg, ← ha]; exact left_mem_segment ℝ _ _
    have hadj1 : (0 : ZMod R.n) + 1 ≠ (m : ZMod R.n) := by
      rw [zero_add]; exact h1nem
    have hadjm1 : (m : ZMod R.n) + 1 ≠ 0 := by
      have he : (m : ZMod R.n) + 1 = (((m + 1 : ℕ)) : ZMod R.n) := by push_cast; ring
      rw [he]
      intro hc'
      have : (((m + 1 : ℕ)) : ZMod R.n).val = (0 : ZMod R.n).val := by rw [hc']
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at this; omega
    have hdisj := hS.2.1 0 (m : ZMod R.n) (Ne.symm hmne0) hadj1 hadjm1
    exact (Set.disjoint_left.mp hdisj hmemE0 hmemEm)

/-- **`hAdjPrev` for an empty ear.** The incoming edge `[vₘ₋₁, vₘ]` and the diagonal
`[vₘ, v₀]` meet exactly at the shared vertex `vₘ`. If they overlapped along a common
ray from `vₘ`, then either `vₘ₋₁ ∈ [vₘ, v₀] ⊆ closed ear-triangle` (empty-ear at `vₘ₋₁`)
or `v₀ ∈ [vₘ₋₁, vₘ] = edge (m-1)` while `v₀ ∈ edge (m+1)` (edges `m-1`, `m+1` being
non-adjacent for `m ≥ 2`, contradicting `R`'s simplicity). -/
lemma diag_adjPrev_inter (R : LatticePolygon) (hS : R.IsSimple) (m : ℕ) (hm : R.n = m + 2)
    (hm2 : 2 ≤ m) (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    segment ℝ (toReal (R.vert (((m - 1 : ℕ)) : ZMod R.n))) (toReal (R.vert (m : ZMod R.n)))
      ∩ segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))
    = {toReal (R.vert (m : ZMod R.n))} := by
  classical
  have hbase := earTri_cross_base_pos R m hm hear
  have hm0 : ((m - 1 : ℕ) : ZMod R.n) + 1 = (m : ZMod R.n) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  -- index facts
  have hmne0 : (m : ZMod R.n) ≠ 0 := by
    intro he
    have : ((m : ZMod R.n)).val = (0 : ZMod R.n).val := by rw [he]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at this; omega
  have hmp1ne0 : (m : ZMod R.n) + 1 ≠ 0 := by
    have he : (m : ZMod R.n) + 1 = (((m + 1 : ℕ)) : ZMod R.n) := by push_cast; ring
    rw [he]; intro hc'
    have : (((m + 1 : ℕ)) : ZMod R.n).val = (0 : ZMod R.n).val := by rw [hc']
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at this; omega
  -- m-1 (as ZMod) facts
  have hm1val : (((m - 1 : ℕ) : ZMod R.n)).val = m - 1 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hm1nem : ((m - 1 : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) := by
    intro he
    have hvm : ((m : ZMod R.n)).val = m := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have : (((m - 1 : ℕ) : ZMod R.n)).val = ((m : ZMod R.n)).val := by rw [he]
    rw [hm1val, hvm] at this; omega
  have hm1ne0 : ((m - 1 : ℕ) : ZMod R.n) ≠ 0 := by
    intro he
    have : (((m - 1 : ℕ) : ZMod R.n)).val = (0 : ZMod R.n).val := by rw [he]
    rw [hm1val, ZMod.val_zero] at this; omega
  have hm1nemp1 : ((m - 1 : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) + 1 := by
    intro he
    have hvmp1 : ((((m + 1 : ℕ)) : ZMod R.n)).val = m + 1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have heq : (m : ZMod R.n) + 1 = (((m + 1 : ℕ)) : ZMod R.n) := by push_cast; ring
    rw [heq] at he
    have : (((m - 1 : ℕ) : ZMod R.n)).val = ((((m + 1 : ℕ)) : ZMod R.n)).val := by rw [he]
    rw [hm1val, hvmp1] at this; omega
  -- vertices distinct
  have hvm10 : R.vert ((m - 1 : ℕ) : ZMod R.n) ≠ R.vert (m : ZMod R.n) :=
    fun he => hm1nem (vert_injective R hS he)
  have hvm0 : R.vert (m : ZMod R.n) ≠ R.vert 0 := fun he => hmne0 (vert_injective R hS he)
  rw [segment_symm ℝ (toReal (R.vert (((m - 1 : ℕ)) : ZMod R.n))) (toReal (R.vert (m : ZMod R.n)))]
  apply segment_inter_eq_endpoint_of_not_sameRay
  intro hsr
  have hne1 : toReal (R.vert ((m - 1 : ℕ) : ZMod R.n)) - toReal (R.vert (m : ZMod R.n)) ≠ 0 := by
    rw [sub_ne_zero]; exact fun he => hvm10 (toReal_injective he)
  have hne2 : toReal (R.vert 0) - toReal (R.vert (m : ZMod R.n)) ≠ 0 := by
    rw [sub_ne_zero]; exact fun he => hvm0 (toReal_injective he).symm
  obtain ⟨r, hr0, hreq⟩ := hsr.exists_pos_left hne1 hne2
  set a := toReal (R.vert ((m - 1 : ℕ) : ZMod R.n)) with ha
  set b := toReal (R.vert (m : ZMod R.n)) with hb
  set c := toReal (R.vert 0) with hc
  rcases le_total 1 r with hr1 | hr1
  · -- vₘ₋₁ ∈ [vₘ, v₀] ⊆ closed ear triangle → empty-ear contradiction at vₘ₋₁
    have hrpos : (0:ℝ) < r := hr0
    have hsinv : (0:ℝ) ≤ 1 / r := by positivity
    have hsinv1 : 1 / r ≤ 1 := by rw [div_le_one hrpos]; exact hr1
    have hmem : a ∈ segment ℝ b c := by
      apply seg_of_affine hsinv hsinv1
      have hac : a - b = (1 / r) • (c - b) := by
        have hh : r • (a - b) = c - b := hreq
        rw [← hh, smul_smul, one_div, inv_mul_cancel₀ hrpos.ne', one_smul]
      rw [smul_sub] at hac
      have ha2 : a = b + ((1/r) • c - (1/r) • b) := by rw [← hac]; abel
      rw [ha2, sub_smul, one_smul]; abel
    have hin : inTriangle b (toReal (R.vert ((m : ZMod R.n) + 1))) c a :=
      inTriangle_of_mem_segment_fst_thd b (toReal (R.vert ((m : ZMod R.n) + 1))) c a hbase.le hmem
    refine hear.2 ((m - 1 : ℕ) : ZMod R.n) ?_ ?_ ?_ ?_
    · show ((m - 1 : ℕ) : ZMod R.n) ≠ ((m : ZMod R.n) + 1) - 1
      rw [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring]; exact hm1nem
    · show ((m - 1 : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) + 1; exact hm1nemp1
    · show ((m - 1 : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) + 1 + 1
      rw [show ((m : ZMod R.n) + 1 + 1) = (0 : ZMod R.n) by
        have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
        push_cast at hz; linear_combination hz]; exact hm1ne0
    · show inTriangle (toReal (R.vert ((m : ZMod R.n) + 1 - 1)))
        (toReal (R.vert ((m : ZMod R.n) + 1)))
        (toReal (R.vert ((m : ZMod R.n) + 1 + 1))) (toReal (R.vert ((m - 1 : ℕ) : ZMod R.n)))
      rw [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring,
        show ((m : ZMod R.n) + 1 + 1) = (0 : ZMod R.n) by
          have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
          push_cast at hz; linear_combination hz]
      exact hin
  · -- v₀ ∈ [vₘ, vₘ₋₁] = edge (m-1), and v₀ ∈ edge (m+1); non-adjacent → disjoint, contra
    have hmem : c ∈ segment ℝ b a := by
      apply seg_of_affine hr0.le hr1
      have hh : c - b = r • (a - b) := hreq.symm
      rw [smul_sub] at hh
      have hc2 : c = b + (r • a - r • b) := by rw [← hh]; abel
      rw [hc2, sub_smul, one_smul]; abel
    have hmemEm1 : c ∈ R.edgeSeg ((m - 1 : ℕ) : ZMod R.n) := by
      rw [LatticePolygon.edgeSeg, hm0, ← hb, ← ha, segment_symm]; exact hmem
    have hmemEmp1 : c ∈ R.edgeSeg ((m : ZMod R.n) + 1) := by
      rw [LatticePolygon.edgeSeg,
        show ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) by
          have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
          push_cast at hz; linear_combination hz, ← hc]
      exact right_mem_segment ℝ _ _
    -- edges (m-1) and (m+1) non-adjacent
    have hne_idx : ((m - 1 : ℕ) : ZMod R.n) ≠ (m : ZMod R.n) + 1 := hm1nemp1
    have h1ne0 : (1 : ZMod R.n) ≠ 0 := by
      have : (1 : ZMod R.n).val = 1 := by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      intro he; rw [he, ZMod.val_zero] at this; omega
    have hadj1 : ((m - 1 : ℕ) : ZMod R.n) + 1 ≠ (m : ZMod R.n) + 1 := by
      rw [hm0]; intro he; exact h1ne0 (by linear_combination -he)
    have hadj2 : ((m : ZMod R.n) + 1) + 1 ≠ ((m - 1 : ℕ) : ZMod R.n) := by
      rw [show ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) by
        have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
        push_cast at hz; linear_combination hz]
      exact (Ne.symm hm1ne0)
    have hdisj := hS.2.1 ((m - 1 : ℕ) : ZMod R.n) ((m : ZMod R.n) + 1) hne_idx hadj1 hadj2
    exact (Set.disjoint_left.mp hdisj hmemEm1 hmemEmp1)

/-! ### The empty-ear diagonal-disjointness core (`diag_disjoint_nonincident_edge`)

For an empty ear `T = (vₘ, vₘ₊₁, v₀)` with base diagonal `D = [vₘ, v₀]`, every edge
`edgeSeg k` non-incident to `T` is disjoint from `D`.  The geometric heart is a
*crossing* lemma: if a segment `[e₀, e₁]` met the **open** base of a positively
oriented triangle while having both endpoints outside the closed triangle, it would
have to cross one of the two *legs* `[a,b]`, `[b,c]`.  We isolate that as
`segment_meets_leg_of_cross_base`, then refute it via `R`'s simplicity (the legs are
non-adjacent `R`-edges, hence disjoint from `edgeSeg k`). -/

/-- **First-exit on a segment for two affine functionals.** Two affine functions
`F i u = (1−u)·α i + u·β i` (`i ∈ {1,2}`) start positive (`α₁, α₂ > 0`) and at least
one ends negative (`β₁ < 0 ∨ β₂ < 0`).  There is a first parameter `u ∈ (0,1]` where
one of them vanishes while the other (and the increasing third functional) stays
nonnegative: `0 ≤ (1−u)α₁ + uβ₁`, `0 ≤ (1−u)α₂ + uβ₂`, and one is `= 0`. -/
private lemma first_exit_two_affine (α1 β1 α2 β2 : ℝ)
    (hα1 : 0 < α1) (hα2 : 0 < α2) (hβ : β1 < 0 ∨ β2 < 0) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧ 0 ≤ (1 - u) * α1 + u * β1 ∧ 0 ≤ (1 - u) * α2 + u * β2 ∧
      ((1 - u) * α1 + u * β1 = 0 ∨ (1 - u) * α2 + u * β2 = 0) := by
  -- candidate zeros: u_i := α_i / (α_i − β_i) when β_i < 0, else 1
  set u1 : ℝ := if β1 < 0 then α1 / (α1 - β1) else 1 with hu1
  set u2 : ℝ := if β2 < 0 then α2 / (α2 - β2) else 1 with hu2
  have hu1pos : 0 < u1 := by
    rw [hu1]; split_ifs with h
    · exact div_pos hα1 (by linarith)
    · norm_num
  have hu2pos : 0 < u2 := by
    rw [hu2]; split_ifs with h
    · exact div_pos hα2 (by linarith)
    · norm_num
  have hu1le : u1 ≤ 1 := by
    rw [hu1]; split_ifs with h
    · rw [div_le_one (by linarith)]; linarith
    · exact le_refl 1
  have hu2le : u2 ≤ 1 := by
    rw [hu2]; split_ifs with h
    · rw [div_le_one (by linarith)]; linarith
    · exact le_refl 1
  -- value of functional i is nonneg on [0, u_i] and zero at u_i (when β_i<0)
  have hval1 : ∀ u, 0 ≤ u → u ≤ u1 → 0 ≤ (1 - u) * α1 + u * β1 := by
    intro u hu0 huu
    rcases le_or_gt (0:ℝ) β1 with hb | hb
    · nlinarith [hu0]
    · rw [hu1, if_pos hb] at huu
      have hden : 0 < α1 - β1 := by linarith
      rw [le_div_iff₀ hden] at huu; nlinarith
  have hval2 : ∀ u, 0 ≤ u → u ≤ u2 → 0 ≤ (1 - u) * α2 + u * β2 := by
    intro u hu0 huu
    rcases le_or_gt (0:ℝ) β2 with hb | hb
    · nlinarith [hu0]
    · rw [hu2, if_pos hb] at huu
      have hden : 0 < α2 - β2 := by linarith
      rw [le_div_iff₀ hden] at huu; nlinarith
  have hz1 : β1 < 0 → (1 - u1) * α1 + u1 * β1 = 0 := by
    intro hb; rw [hu1, if_pos hb]
    have hden : α1 - β1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have hz2 : β2 < 0 → (1 - u2) * α2 + u2 * β2 = 0 := by
    intro hb; rw [hu2, if_pos hb]
    have hden : α2 - β2 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  rcases le_total u1 u2 with hle | hle
  · -- u1 ≤ u2: exit via functional 1.  Need β1 < 0 (so the zero is genuine).
    rcases le_or_gt (0:ℝ) β1 with hb1 | hb1
    · -- β1 ≥ 0 ⟹ β2 < 0, and u2 = its zero; but u1 ≤ u2 with u1 = 1 ≥ u2, so u2 = 1 = u1
      have hb2 : β2 < 0 := hβ.resolve_left (by simpa using hb1)
      have hu1one : u1 = 1 := by rw [hu1, if_neg (by simpa using hb1)]
      have : u2 = 1 := le_antisymm hu2le (hu1one ▸ hle)
      refine ⟨u2, hu2pos, hu2le, ?_, ?_, Or.inr (hz2 hb2)⟩
      · exact hval1 u2 hu2pos.le (by rw [this, hu1one])
      · exact hval2 u2 hu2pos.le (le_refl u2)
    · refine ⟨u1, hu1pos, hu1le, le_of_eq (hz1 hb1).symm, hval2 u1 hu1pos.le hle, Or.inl (hz1 hb1)⟩
  · -- u2 ≤ u1: exit via functional 2
    rcases le_or_gt (0:ℝ) β2 with hb2 | hb2
    · have hb1 : β1 < 0 := hβ.resolve_right (by simpa using hb2)
      have hu2one : u2 = 1 := by rw [hu2, if_neg (by simpa using hb2)]
      have : u1 = 1 := le_antisymm hu1le (hu2one ▸ hle)
      refine ⟨u1, hu1pos, hu1le, ?_, ?_, Or.inl (hz1 hb1)⟩
      · exact hval1 u1 hu1pos.le (le_refl u1)
      · exact hval2 u1 hu1pos.le (by rw [this, hu2one])
    · refine ⟨u2, hu2pos, hu2le, hval1 u2 hu2pos.le hle, le_of_eq (hz2 hb2).symm, Or.inr (hz2 hb2)⟩

/-- A planar cross functional `x ↦ cross u (x − w)` is affine along a segment:
its value at `(1−s)•e₀ + s•e₁` is `(1−s)·(value at e₀) + s·(value at e₁)`. -/
private lemma cross_affine_seg (u w e0 e1 : ℝ × ℝ) (s : ℝ) :
    cross u (((1 - s) • e0 + s • e1) - w)
      = (1 - s) * cross u (e0 - w) + s * cross u (e1 - w) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- A point of a closed segment distinct from both endpoints lies in the open segment. -/
private lemma mem_openSegment_of_ne_endpoints {a c p : ℝ × ℝ}
    (h : p ∈ segment ℝ a c) (h1 : p ≠ a) (h2 : p ≠ c) : p ∈ openSegment ℝ a c := by
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := h
  refine ⟨x, y, ?_, ?_, hxy, hp⟩
  · rcases eq_or_lt_of_le hx with he | he
    · exfalso; apply h2; rw [← hp, ← he]; simp; rw [show y = 1 by linarith]; simp
    · exact he
  · rcases eq_or_lt_of_le hy with he | he
    · exfalso; apply h1; rw [← hp, ← he]; simp; rw [show x = 1 by linarith]; simp
    · exact he

/-- Two vectors that are both parallel to a common nonzero vector `d`
(`cross d u = cross d v = 0`) are parallel to each other. -/
private lemma cross_eq_zero_of_common_parallel (d u v : ℝ × ℝ)
    (h1 : cross d u = 0) (h2 : cross d v = 0) (hd : d ≠ 0) : cross u v = 0 := by
  rcases (not_and_or.mp (fun h => hd (Prod.ext h.1 h.2)) : d.1 ≠ 0 ∨ d.2 ≠ 0) with hd1 | hd2
  · have : cross u v * d.1 = u.1 * cross d v - v.1 * cross d u := by simp only [cross]; ring
    rw [h1, h2] at this; simp at this; rcases this with h | h
    · exact h
    · exact absurd h hd1
  · have : cross u v * d.2 = u.2 * cross d v - v.2 * cross d u := by simp only [cross]; ring
    rw [h1, h2] at this; simp at this; rcases this with h | h
    · exact h
    · exact absurd h hd2

/-- The three sub-triangle cross areas at a point `z` sum to the total signed area. -/
private lemma cross_bary_sum (a b c z : ℝ × ℝ) :
    cross (b - a) (z - a) + cross (c - b) (z - b) + cross (a - c) (z - c)
      = cross (b - a) (c - a) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- **A point of the closed triangle on the line `a–b` lies on the edge `[a, b]`.**
If `inTriangle a b c z` and `z` is on the line through `a, b`
(`cross (b−a) (z−a) = 0`), then `z ∈ segment ℝ a b`.  The barycentric weight is
`r = cross (a−c) (z−c) / D` with `D = cross (b−a) (c−a) > 0`. -/
lemma mem_segment_ab_of_inTriangle_f1_zero (a b c z : ℝ × ℝ)
    (hD : 0 < cross (b - a) (c - a)) (hz : inTriangle a b c z)
    (hf1 : cross (b - a) (z - a) = 0) : z ∈ segment ℝ a b := by
  obtain ⟨_, hf2, hf3⟩ := hz
  set D := cross (b - a) (c - a) with hDdef
  set r := cross (a - c) (z - c) / D with hrdef
  have hr0 : 0 ≤ r := div_nonneg hf3 hD.le
  have hsum := cross_bary_sum a b c z
  rw [hf1] at hsum
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one hD]; nlinarith [hf2]
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  -- z = (1-r) • a + r • b, proved coordinatewise
  have heq1 : (z.1 - a.1) * D = cross (a - c) (z - c) * (b.1 - a.1) := by
    have := hf1; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (c.1 - a.1) * this
  have heq2 : (z.2 - a.2) * D = cross (a - c) (z - c) * (b.2 - a.2) := by
    have := hf1; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (c.2 - a.2) * this
  have hDne : D ≠ 0 := ne_of_gt hD
  apply Prod.ext
  · show ((1 - r) • a + r • b).1 = z.1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [hrdef]; field_simp; linarith [heq1]
  · show ((1 - r) • a + r • b).2 = z.2
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hrdef]; field_simp; linarith [heq2]

/-- **A point of the closed triangle on the line `b–c` lies on the edge `[b, c]`.** -/
lemma mem_segment_bc_of_inTriangle_f2_zero (a b c z : ℝ × ℝ)
    (hD : 0 < cross (b - a) (c - a)) (hz : inTriangle a b c z)
    (hf2 : cross (c - b) (z - b) = 0) : z ∈ segment ℝ b c := by
  obtain ⟨hf1, _, hf3⟩ := hz
  set D := cross (b - a) (c - a) with hDdef
  -- weight along [b,c]: r = cross (b-a) (z-a) / D
  set r := cross (b - a) (z - a) / D with hrdef
  have hr0 : 0 ≤ r := div_nonneg hf1 hD.le
  have hsum := cross_bary_sum a b c z
  rw [hf2] at hsum
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one hD]; nlinarith [hf3]
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  have hDcb : cross (c - b) (a - b) = D := by
    simp only [hDdef, cross, Prod.fst_sub, Prod.snd_sub]; ring
  have heq1 : (z.1 - b.1) * D = cross (b - a) (z - a) * (c.1 - b.1) := by
    have := hf2; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (a.1 - b.1) * this
  have heq2 : (z.2 - b.2) * D = cross (b - a) (z - a) * (c.2 - b.2) := by
    have := hf2; simp only [cross, Prod.fst_sub, Prod.snd_sub] at this hDdef ⊢
    rw [hDdef]; linear_combination (a.2 - b.2) * this
  have hDne : D ≠ 0 := ne_of_gt hD
  apply Prod.ext
  · show ((1 - r) • b + r • c).1 = z.1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [hrdef]; field_simp; linarith [heq1]
  · show ((1 - r) • b + r • c).2 = z.2
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hrdef]; field_simp; linarith [heq2]

/-- **A point of the closed triangle on the line `c–a` lies on the edge `[c, a]`.**
The cyclic image of `mem_segment_ab_of_inTriangle_f1_zero` applied to `(c, a, b)`. -/
lemma mem_segment_ca_of_inTriangle_f3_zero (a b c z : ℝ × ℝ)
    (hD : 0 < cross (b - a) (c - a)) (hz : inTriangle a b c z)
    (hf3 : cross (a - c) (z - c) = 0) : z ∈ segment ℝ c a := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine mem_segment_ab_of_inTriangle_f1_zero c a b z ?_ ⟨h3, h1, h2⟩ hf3
  have he : cross (a - c) (b - c) = cross (b - a) (c - a) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  rw [he]; exact hD

/-- **Collinear betweenness gives segment membership.** If `w` lies on the line
through `e₀, e₁` (`cross (e₁−e₀) (w−e₀) = 0`) and a fixed functional `cross u (· − w)`
is strictly negative at `e₀` and strictly positive at `e₁`, then `w ∈ [e₀, e₁]`. -/
private lemma mem_segment_of_collinear_between (u e0 e1 w : ℝ × ℝ)
    (hcol : cross (e1 - e0) (w - e0) = 0)
    (hg0 : cross u (e0 - w) < 0) (hg1 : 0 < cross u (e1 - w)) :
    w ∈ segment ℝ e0 e1 := by
  set g0 := cross u (e0 - w) with hg0def
  set g1 := cross u (e1 - w) with hg1def
  set den := g1 - g0 with hdendef
  have hden : 0 < den := by rw [hdendef]; linarith
  have hdeneq : cross u (e1 - e0) = den := by
    rw [hdendef, hg1def, hg0def]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hcol' : (e1.1 - e0.1) * (w.2 - e0.2) - (e1.2 - e0.2) * (w.1 - e0.1) = 0 := by
    have := hcol; simpa only [cross, Prod.fst_sub, Prod.snd_sub] using this
  have hdne : den ≠ 0 := ne_of_gt hden
  refine ⟨g1 / den, -g0 / den, by positivity, by
    rw [div_nonneg_iff]; left; exact ⟨by linarith, hden.le⟩, ?_, ?_⟩
  · field_simp; rw [hdendef]; ring
  · -- w = (g1/den) • e0 + (-g0/den) • e1
    have hx : w.1 * cross u (e1 - e0) = cross u (e1 - w) * e0.1 - cross u (e0 - w) * e1.1 := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; linear_combination (-u.1) * hcol'
    have hy : w.2 * cross u (e1 - e0) = cross u (e1 - w) * e0.2 - cross u (e0 - w) * e1.2 := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; linear_combination (-u.2) * hcol'
    rw [hdeneq] at hx hy
    apply Prod.ext
    · show ((g1 / den) • e0 + (-g0 / den) • e1).1 = w.1
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [hg1def, hg0def]; field_simp; linarith [hx]
    · show ((g1 / den) • e0 + (-g0 / den) • e1).2 = w.2
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hg1def, hg0def]; field_simp; linarith [hy]

/-- **Crossing lemma.** Let `T = (a, b, c)` be a positively oriented triangle
(`0 < cross (b−a) (c−a)`), with both `e₀, e₁` outside the closed triangle.  If a
point `p` lies on the **open** base `openSegment ℝ a c` and on the segment
`[e₀, e₁]`, then `[e₀, e₁]` meets one of the two legs `[a, b]` or `[b, c]`.

The proof: `p` lies in the relative interior of the base, so `f₁ p, f₂ p > 0` and
`f₃ p = 0` where `f₁ x = cross (b−a) (x−a)`, `f₂ x = cross (c−b) (x−b)`,
`f₃ x = cross (a−c) (x−c)`.  Since `p ∈ segment e₀ e₁` but `p ∉ {e₀, e₁}` (both are
outside the triangle while `p` is on the base ⊆ triangle), `p` is in the *open*
segment, so the two endpoints lie strictly on opposite sides of the base line
(`f₃`).  Picking the endpoint `e⁺` on the apex side (`f₃ e⁺ > 0`), it is outside the
triangle, so `f₁ e⁺ < 0` or `f₂ e⁺ < 0`.  Walking from `p` to `e⁺`, the first of
`f₁`, `f₂` to vanish gives a point `z` of `[p, e⁺] ⊆ [e₀, e₁]` on the corresponding
leg (`z ∈ T` with one of `f₁ z, f₂ z = 0`). -/
lemma segment_meets_leg_of_cross_base (a b c e0 e1 : ℝ × ℝ)
    (hbase : 0 < cross (b - a) (c - a))
    (he0 : ¬ inTriangle a b c e0) (he1 : ¬ inTriangle a b c e1)
    (p : ℝ × ℝ) (hpD : p ∈ openSegment ℝ a c) (hpj : p ∈ segment ℝ e0 e1) :
    (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ a b) ∨
    (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ b c) ∨
    a ∈ segment ℝ e0 e1 ∨ c ∈ segment ℝ e0 e1 := by
  -- abbreviations for the three half-plane cross functionals
  set f1 : ℝ × ℝ → ℝ := fun x => cross (b - a) (x - a) with hf1
  set f2 : ℝ × ℝ → ℝ := fun x => cross (c - b) (x - b) with hf2
  set f3 : ℝ × ℝ → ℝ := fun x => cross (a - c) (x - c) with hf3
  -- inTriangle in terms of f1,f2,f3
  have hinTri : ∀ x, inTriangle a b c x ↔ 0 ≤ f1 x ∧ 0 ≤ f2 x ∧ 0 ≤ f3 x := by
    intro x; rfl
  -- p lies in the closed triangle (it is on the base segment)
  have hpT : inTriangle a b c p :=
    inTriangle_of_mem_segment_fst_thd a b c p hbase.le (openSegment_subset_segment ℝ a c hpD)
  -- p on the open base: p = (1-t)a + t c, 0 < t < 1
  rw [openSegment_eq_image] at hpD
  obtain ⟨t, ⟨ht0, ht1⟩, hpt⟩ := hpD
  have hpa : p = (1 - t) • a + t • c := by rw [← hpt]
  -- values of f1,f2,f3 at p
  have hf1p : f1 p = t * cross (b - a) (c - a) := by
    rw [hf1, hpa]
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hf2p : f2 p = (1 - t) * cross (b - a) (c - a) := by
    rw [hf2, hpa]
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hf3p : f3 p = 0 := by
    rw [hf3, hpa]
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hf1p_pos : 0 < f1 p := by rw [hf1p]; positivity
  have hf2p_pos : 0 < f2 p := by rw [hf2p]; exact mul_pos (by linarith) hbase
  -- p = (1-s) e0 + s e1
  rw [segment_eq_image] at hpj
  obtain ⟨s, ⟨hs0, hs1⟩, hps⟩ := hpj
  have hps' : p = (1 - s) • e0 + s • e1 := by rw [← hps]
  -- s ∉ {0,1}: otherwise p = e0 or e1, both outside the triangle
  have hsne0 : s ≠ 0 := by
    rintro rfl
    apply he0; simpa [hps'] using hpT
  have hsne1 : s ≠ 1 := by
    rintro rfl
    apply he1; simpa [hps'] using hpT
  have hs0' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsne0)
  have hs1' : s < 1 := lt_of_le_of_ne hs1 hsne1
  -- affine decomposition of each functional along [e0,e1]
  have hf1s : f1 p = (1 - s) * f1 e0 + s * f1 e1 := by rw [hf1, hps']; exact cross_affine_seg _ _ _ _ _
  have hf2s : f2 p = (1 - s) * f2 e0 + s * f2 e1 := by rw [hf2, hps']; exact cross_affine_seg _ _ _ _ _
  have hf3s : f3 p = (1 - s) * f3 e0 + s * f3 e1 := by rw [hf3, hps']; exact cross_affine_seg _ _ _ _ _
  -- f3 p = 0, so (1-s) f3 e0 + s f3 e1 = 0
  have hf3sum : (1 - s) * f3 e0 + s * f3 e1 = 0 := by rw [← hf3s, hf3p]
  -- p ∈ segment e0 e1 (reconstructed)
  have hpseg : p ∈ segment ℝ e0 e1 := ⟨1 - s, s, by linarith, hs0, by ring, by rw [← hps']⟩
  -- the apex walk: an endpoint `e` on the apex side (`f3 e > 0`, outside `T`) forces a
  -- leg crossing of `[e0,e1]`
  have apexWalk : ∀ e : ℝ × ℝ, e ∈ segment ℝ e0 e1 → 0 < f3 e → ¬ inTriangle a b c e →
      (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ a b) ∨
      (∃ q ∈ segment ℝ e0 e1, q ∈ segment ℝ b c) := by
    intro e heseg hf3e hnotT
    -- ¬inTriangle e with f3 e > 0 gives f1 e < 0 ∨ f2 e < 0
    have hβ : f1 e < 0 ∨ f2 e < 0 := by
      by_contra hc
      push Not at hc
      exact hnotT ((hinTri e).mpr ⟨hc.1, hc.2, hf3e.le⟩)
    obtain ⟨u, hu0, hule, hv1, hv2, hzero⟩ :=
      first_exit_two_affine (f1 p) (f1 e) (f2 p) (f2 e) hf1p_pos hf2p_pos hβ
    -- z = (1-u) p + u e
    set z := (1 - u) • p + u • e with hzdef
    have hzseg : z ∈ segment ℝ e0 e1 :=
      convex_segment e0 e1 hpseg heseg (by linarith) hu0.le (by ring)
    have hf1z : f1 z = (1 - u) * f1 p + u * f1 e := by rw [hf1, hzdef]; exact cross_affine_seg _ _ _ _ _
    have hf2z : f2 z = (1 - u) * f2 p + u * f2 e := by rw [hf2, hzdef]; exact cross_affine_seg _ _ _ _ _
    have hf3z : f3 z = (1 - u) * f3 p + u * f3 e := by rw [hf3, hzdef]; exact cross_affine_seg _ _ _ _ _
    have hf3znn : 0 ≤ f3 z := by rw [hf3z, hf3p]; positivity
    have hzT : inTriangle a b c z :=
      (hinTri z).mpr ⟨by rw [hf1z]; exact hv1, by rw [hf2z]; exact hv2, hf3znn⟩
    rcases hzero with h0 | h0
    · left
      exact ⟨z, hzseg, mem_segment_ab_of_inTriangle_f1_zero a b c z hbase hzT (by rw [← hf1z] at h0; exact h0)⟩
    · right
      exact ⟨z, hzseg, mem_segment_bc_of_inTriangle_f2_zero a b c z hbase hzT (by rw [← hf2z] at h0; exact h0)⟩
  -- endpoints lie in segment e0 e1
  have he0seg : e0 ∈ segment ℝ e0 e1 := left_mem_segment ℝ e0 e1
  have he1seg : e1 ∈ segment ℝ e0 e1 := right_mem_segment ℝ e0 e1
  -- dispatch on the sign of f3 at the endpoints
  rcases lt_trichotomy (f3 e0) 0 with hg0 | hg0 | hg0
  · -- f3 e0 < 0 ⟹ f3 e1 > 0 (apex side)
    have hg1 : 0 < f3 e1 := by nlinarith [hf3sum]
    rcases apexWalk e1 he1seg hg1 he1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · -- f3 e0 = 0 ⟹ f3 e1 = 0 (collinear): both a, c ∈ segment e0 e1
    have hg1 : f3 e1 = 0 := by
      have : s * f3 e1 = 0 := by rw [hg0] at hf3sum; linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hs0')
      · exact h
    -- collinear case: a, e0, e1 on the base line {f3 = 0}; show a ∈ segment e0 e1.
    right; right; left
    -- barycentric: f1 + f2 + f3 = D, and f3 e0 = f3 e1 = 0
    have hD : (0:ℝ) < cross (b - a) (c - a) := hbase
    have hbary0 := cross_bary_sum a b c e0
    have hbary1 := cross_bary_sum a b c e1
    have hf3e0 : f3 e0 = cross (a - c) (e0 - c) := by rw [hf3]
    have hf3e1 : f3 e1 = cross (a - c) (e1 - c) := by rw [hf3]
    -- f2 e_i = D - f1 e_i (since f3 e_i = 0)
    have hf2e0 : f2 e0 = cross (b - a) (c - a) - f1 e0 := by
      have : f1 e0 + f2 e0 + f3 e0 = cross (b - a) (c - a) := hbary0
      rw [hg0] at this; linarith
    have hf2e1 : f2 e1 = cross (b - a) (c - a) - f1 e1 := by
      have : f1 e1 + f2 e1 + f3 e1 = cross (b - a) (c - a) := hbary1
      rw [hg1] at this; linarith
    -- f1 e0, f1 e1 each avoid [0, D]
    have hout0 : f1 e0 < 0 ∨ cross (b - a) (c - a) < f1 e0 := by
      rcases lt_or_ge (f1 e0) 0 with h | h
      · exact Or.inl h
      · right; by_contra hc; push Not at hc
        exact he0 ((hinTri e0).mpr ⟨h, by rw [hf2e0]; linarith, le_of_eq hg0.symm⟩)
    have hout1 : f1 e1 < 0 ∨ cross (b - a) (c - a) < f1 e1 := by
      rcases lt_or_ge (f1 e1) 0 with h | h
      · exact Or.inl h
      · right; by_contra hc; push Not at hc
        exact he1 ((hinTri e1).mpr ⟨h, by rw [hf2e1]; linarith, le_of_eq hg1.symm⟩)
    -- f1 p = (1-s) f1 e0 + s f1 e1 ∈ (0, D)
    have hf1plt : f1 p < cross (b - a) (c - a) := by rw [hf1p]; nlinarith [ht1, hD]
    -- collinearity of a on line e0 e1: e1-e0, a-e0 both parallel to (a-c) ≠ 0
    have hac : a - c ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [h] at hD; simp only [cross, sub_self] at hD; simp at hD
    have hpar1 : cross (a - c) (e1 - e0) = 0 := by
      have h0 : cross (a - c) (e0 - c) = 0 := by rw [← hf3e0]; exact hg0
      have h1 : cross (a - c) (e1 - c) = 0 := by rw [← hf3e1]; exact hg1
      simp only [cross, Prod.fst_sub, Prod.snd_sub] at h0 h1 ⊢; linear_combination h1 - h0
    have hpar2 : cross (a - c) (a - e0) = 0 := by
      have h0 : cross (a - c) (e0 - c) = 0 := by rw [← hf3e0]; exact hg0
      simp only [cross, Prod.fst_sub, Prod.snd_sub] at h0 ⊢; linear_combination -h0
    have hcolA : cross (e1 - e0) (a - e0) = 0 :=
      cross_eq_zero_of_common_parallel (a - c) (e1 - e0) (a - e0) hpar1 hpar2 hac
    -- straddle: one of f1 e0, f1 e1 < 0, the other > D
    have hf1e0 : f1 e0 = cross (b - a) (e0 - a) := by rw [hf1]
    have hf1e1 : f1 e1 = cross (b - a) (e1 - a) := by rw [hf1]
    rcases hout0 with hlt0 | hgt0
    · -- f1 e0 < 0 ⟹ f1 e1 > D (else combo ≤ 0)
      have hgt1 : cross (b - a) (c - a) < f1 e1 := by
        rcases hout1 with h | h
        · exfalso; nlinarith [hf1p_pos, hf1s, hs0, hs1, hs0', hs1']
        · exact h
      exact mem_segment_of_collinear_between (b - a) e0 e1 a hcolA
        (by rw [← hf1e0]; exact hlt0) (by rw [← hf1e1]; linarith)
    · -- f1 e0 > D ⟹ f1 e1 < 0; swap roles of e0, e1
      have hlt1 : f1 e1 < 0 := by
        rcases hout1 with h | h
        · exact h
        · exfalso; nlinarith [hf1plt, hf1s, hs0, hs1, hs0', hs1']
      have hcolA' : cross (e0 - e1) (a - e1) = 0 :=
        cross_eq_zero_of_common_parallel (a - c) (e0 - e1) (a - e1)
          (by simp only [cross, Prod.fst_sub, Prod.snd_sub] at hpar1 ⊢; linear_combination -hpar1)
          (by
            have h1 : cross (a - c) (e1 - c) = 0 := by rw [← hf3e1]; exact hg1
            simp only [cross, Prod.fst_sub, Prod.snd_sub] at h1 ⊢; linear_combination -h1)
          hac
      rw [segment_symm]
      exact mem_segment_of_collinear_between (b - a) e1 e0 a hcolA'
        (by rw [← hf1e1]; exact hlt1) (by rw [← hf1e0]; linarith)
  · -- f3 e0 > 0 (apex side)
    rcases apexWalk e0 he0seg hg0 he0 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **The empty-ear diagonal-disjointness core.** For an empty ear at apex `m+1`
(triangle `T = (vₘ, vₘ₊₁, v₀)`, base diagonal `D = [vₘ, v₀]`), every edge `edgeSeg k`
of `R` whose index is *non-incident* to `T` (`k ∉ {m−1, m, m+1, 0}`) is disjoint from
the diagonal `D`.  The two diagonal endpoints `vₘ, v₀` are off `edgeSeg k`
(`vert_notMem_edgeSeg`); any interior crossing point would, by
`segment_meets_leg_of_cross_base`, force `edgeSeg k` to meet one of the ear's two legs
`edgeSeg m = [vₘ, vₘ₊₁]`, `edgeSeg (m+1) = [vₘ₊₁, v₀]` — impossible, as `k` is
non-adjacent to both, so `R`'s simplicity makes them disjoint. -/
lemma diag_disjoint_nonincident_edge (R : LatticePolygon) (hS : R.IsSimple)
    (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1))
    (k : ZMod R.n) (hk1 : k ≠ (m : ZMod R.n) - 1) (hkm : k ≠ (m : ZMod R.n))
    (hkmp1 : k ≠ (m : ZMod R.n) + 1) (hk0 : k ≠ 0) :
    Disjoint (segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert 0))) (R.edgeSeg k) := by
  classical
  have hbase := earTri_cross_base_pos R m hm hear
  -- index identities
  have hmp1mp1 : ((m : ZMod R.n) + 1) + 1 = (0 : ZMod R.n) := by
    have hz : ((m + 2 : ℕ) : ZMod R.n) = 0 := by rw [← hm]; exact ZMod.natCast_self R.n
    push_cast at hz; linear_combination hz
  have hmm1 : (m : ZMod R.n) - 1 = ((m - 1 : ℕ) : ZMod R.n) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  -- the two legs as segments
  have hlegPrev : R.edgeSeg (m : ZMod R.n)
      = segment ℝ (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert ((m : ZMod R.n) + 1))) := by
    rw [LatticePolygon.edgeSeg]
  have hlegNext : R.edgeSeg ((m : ZMod R.n) + 1)
      = segment ℝ (toReal (R.vert ((m : ZMod R.n) + 1))) (toReal (R.vert 0)) := by
    rw [LatticePolygon.edgeSeg, hmp1mp1]
  -- successor-index inequalities (all from k ∉ {m-1, m, m+1, 0})
  have hk0m1 : k ≠ (0 : ZMod R.n) - 1 := by
    rw [show (0 : ZMod R.n) - 1 = (m : ZMod R.n) + 1 by linear_combination -hmp1mp1]; exact hkmp1
  have hkp1_ne_m : k + 1 ≠ (m : ZMod R.n) := fun he => hk1 (by linear_combination he)
  have hkp1_ne_mp1 : k + 1 ≠ (m : ZMod R.n) + 1 := fun he => hkm (by linear_combination he)
  have hkp1_ne_0 : k + 1 ≠ 0 := fun he => hkmp1 (by
    rw [show (m : ZMod R.n) + 1 = ((m : ZMod R.n) + 1 + 1) - 1 by ring, hmp1mp1]
    linear_combination he)
  -- edge k disjoint from the two legs (non-adjacency from k ∉ {m-1,m,m+1,0})
  have hdisjPrev : Disjoint (R.edgeSeg k) (R.edgeSeg (m : ZMod R.n)) :=
    hS.2.1 k (m : ZMod R.n) hkm hkp1_ne_m (fun he => hkmp1 he.symm)
  have hdisjNext : Disjoint (R.edgeSeg k) (R.edgeSeg ((m : ZMod R.n) + 1)) :=
    hS.2.1 k ((m : ZMod R.n) + 1) hkmp1 hkp1_ne_mp1 (by rw [hmp1mp1]; exact fun he => hk0 he.symm)
  -- empty-ear: foreign vertices not in the closed triangle
  have hnotInTri : ∀ j : ZMod R.n, j ≠ (m : ZMod R.n) → j ≠ (m : ZMod R.n) + 1 → j ≠ 0 →
      ¬ inTriangle (toReal (R.vert (m : ZMod R.n))) (toReal (R.vert ((m : ZMod R.n) + 1)))
        (toReal (R.vert 0)) (toReal (R.vert j)) := by
    intro j hjm hjmp1 hj0
    have := hear.2 j (by rw [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring]; exact hjm)
      hjmp1 (by rw [hmp1mp1]; exact hj0)
    rw [show ((m : ZMod R.n) + 1) - 1 = (m : ZMod R.n) by ring, hmp1mp1] at this
    exact this
  -- the two diagonal endpoints are off edge k
  have hkmem : toReal (R.vert (m : ZMod R.n)) ∉ R.edgeSeg k :=
    vert_notMem_edgeSeg R hS (m : ZMod R.n) k hkm hk1
  have hc0mem : toReal (R.vert 0) ∉ R.edgeSeg k :=
    vert_notMem_edgeSeg R hS 0 k hk0 hk0m1
  -- now the disjointness
  rw [Set.disjoint_left]
  intro p hpD hpk
  set a := toReal (R.vert (m : ZMod R.n)) with ha
  set b := toReal (R.vert ((m : ZMod R.n) + 1)) with hb
  set c := toReal (R.vert 0) with hc
  -- p ≠ a, p ≠ c (else an endpoint would lie on edge k)
  have hpa : p ≠ a := fun he => hkmem (he ▸ hpk)
  have hpc : p ≠ c := fun he => hc0mem (he ▸ hpk)
  have hpopen : p ∈ openSegment ℝ a c := mem_openSegment_of_ne_endpoints hpD hpa hpc
  -- edge k as a segment v_k → v_{k+1}
  have hpk' : p ∈ segment ℝ (toReal (R.vert k)) (toReal (R.vert (k + 1))) := by
    rw [LatticePolygon.edgeSeg] at hpk; exact hpk
  -- apply the crossing lemma
  have hcross := segment_meets_leg_of_cross_base a b c
    (toReal (R.vert k)) (toReal (R.vert (k + 1))) hbase
    (hnotInTri k hkm hkmp1 hk0)
    (hnotInTri (k + 1) hkp1_ne_m hkp1_ne_mp1 hkp1_ne_0)
    p hpopen hpk'
  -- segment v_k v_{k+1} = edgeSeg k
  have hek : R.edgeSeg k = segment ℝ (toReal (R.vert k)) (toReal (R.vert (k + 1))) := by
    rw [LatticePolygon.edgeSeg]
  rcases hcross with ⟨q, hqk, hqab⟩ | ⟨q, hqk, hqbc⟩ | haseg | hcseg
  · exact Set.disjoint_left.mp hdisjPrev (hek ▸ hqk) (hlegPrev ▸ hqab)
  · exact Set.disjoint_left.mp hdisjNext (hek ▸ hqk) (hlegNext ▸ hqbc)
  · exact hkmem (hek ▸ haseg)
  · exact hc0mem (hek ▸ hcseg)

/-- **`deleteLast` of an empty ear is simple (Hopf-free).** Specialization of
`deleteLast_isSimple_of_ear` for an *empty ear* at apex `m+1` (`isEarVertex R (m+1)`,
`m ≥ 2`): all three geometric inputs are discharged — the two turn obligations
(`hAdjPrev`/`hAdjNext`) via `diag_adjPrev_inter`/`diag_adjNext_inter`, and the
diagonal–non-incident-edge disjointness `hDisj` via `diag_disjoint_nonincident_edge`.
No external hypothesis remains. -/
lemma deleteLast_isSimple_of_emptyEar (R : LatticePolygon) (hS : R.IsSimple)
    (h2 : 2 ≤ R.n) (m : ℕ) (hm : R.n = m + 2) (hm2 : 2 ≤ m)
    (hear : isEarVertex R ((m : ZMod R.n) + 1)) :
    (deleteLast R h2).IsSimple :=
  deleteLast_isSimple_of_ear R hS h2 m hm (by omega)
    (diag_adjPrev_inter R hS m hm hm2 hear)
    (diag_adjNext_inter R hS m hm hm2 hear)
    (fun k hk1 hkm hkmp1 hk0 => diag_disjoint_nonincident_edge R hS m hm hm2 hear k hk1 hkm hkmp1 hk0)

end Pick
