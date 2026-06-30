import JordanPick.PicksTheorem.Pick.Reductions

/-!
# Pick's theorem: alternation core (Module 2)

The `AlternationCore` namespace plus STEP 1/4/A/B. The chunk reopens
`namespace Pick` (closed at the bottom of this file).
-/

/-! ### Alternation core (combinatorial heart of general-`n` Jordan)

The general-`n` `winding ∈ {0,1}` dichotomy reduces, at a generic height `y`, to
the alternation of the signed ray-crossings sorted by their `x`-threshold: a
right-to-left running sum of `±1` jumps stays in `{0,1}` iff the signs alternate
`+,-,+,-,…` (equivalently `-,+,-,+,…` read left-to-right). The lemmas here are
the **proven combinatorial content** of that alternation; the single remaining
*geometric* input is that an `IsSimple` polygon's crossings alternate. -/

namespace AlternationCore

/-- A list of `±1` signs *alternates* (consecutive entries differ in sign). -/
def Alternates : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => b = -a ∧ Alternates (b :: t)

/-- For an alternating list, the head determines the parity pattern of prefix
sums: if the list starts with value `v ∈ {±1}` then `(L.take k).sum` is `0` when
`k` is even and `v` when `k` is odd (for any `k`, clamped by the length but the
alternation makes the formula hold throughout). We track it via the running head
value. -/
lemma take_sum_eq_of_alternates : ∀ (L : List ℤ) (v : ℤ), Alternates L →
    (L ≠ [] → L.headI = v) → ∀ k,
    (L.take k).sum = (if Even (min k L.length) then 0 else v) := by
  intro L
  induction L using List.rec with
  | nil => intro v _ _ k; simp
  | cons a t IH =>
    intro v halt hhead k
    cases k with
    | zero => simp
    | succ k =>
      have hav : a = v := by simpa using hhead (by simp)
      subst hav
      cases t with
      | nil => cases k <;> simp [Nat.even_add_one, parity_simps]
      | cons b s =>
        -- alternation: b = -a, and (b :: s) alternates
        obtain ⟨hb, halts⟩ := halt
        have hIH := IH (-a) halts (by intro _; simpa using hb) k
        rw [List.take_succ_cons, List.sum_cons, hIH]
        simp only [List.length_cons]
        have hmin : min (k + 1) (s.length + 1 + 1) = min k (s.length + 1) + 1 := by omega
        rcases Nat.even_or_odd (min k (s.length + 1)) with he | ho
        · rw [if_pos he, if_neg (by rw [hmin]; simpa [Nat.even_add_one] using he)]
          ring
        · rw [if_neg (by simpa [Nat.not_even_iff_odd] using ho),
            if_pos (by rw [hmin]; simpa [Nat.even_add_one, Nat.not_even_iff_odd] using ho)]
          ring

/-- **Suffix sums of an alternating crossing list lie in `{0,1}`.** If an
alternating `±1` list starts with `-1`, every prefix sum is `0` or `-1`; hence
every *suffix* sum (the running winding count, swept right-to-left) is `0` or `1`.
This is the combinatorial content the geometric alternation supplies. -/
lemma prefixSums_mem_neg : ∀ (L : List ℤ), Alternates L →
    (L ≠ [] → L.headI = -1) →
    ∀ k, (L.take k).sum = 0 ∨ (L.take k).sum = -1 := by
  intro L halt hhead k
  rw [take_sum_eq_of_alternates L (-1) halt hhead k]
  split_ifs <;> [left; right] <;> rfl

/-- **Suffix sums of an alternating list with head `-1` and total sum `0` lie in
`{0,1}`.** Since `(L.drop k).sum = L.sum - (L.take k).sum = -(L.take k).sum`, and
prefix sums are in `{0,-1}`, suffix sums are in `{0,1}`. This is the form the
right-to-left winding sweep consumes. -/
lemma suffixSums_mem : ∀ (L : List ℤ), Alternates L →
    (L ≠ [] → L.headI = -1) → L.sum = 0 →
    ∀ k, (L.drop k).sum = 0 ∨ (L.drop k).sum = 1 := by
  intro L halt hhead hsum k
  have hsplit : (L.take k).sum + (L.drop k).sum = 0 := by
    rw [← List.sum_append, List.take_append_drop]; exact hsum
  rcases prefixSums_mem_neg L halt hhead k with h | h
  · left; omega
  · right; omega

/-- **Mirror suffix bound (head `+1`).** If an alternating `±1` list starts with
`+1` and sums to `0`, then every suffix sum lies in `{0,-1}`. (Prefix sums are in
`{0,1}` by `take_sum_eq_of_alternates`; suffix `= -prefix`.) -/
lemma suffixSums_mem_nonpos : ∀ (L : List ℤ), Alternates L →
    (L ≠ [] → L.headI = 1) → L.sum = 0 →
    ∀ k, (L.drop k).sum = 0 ∨ (L.drop k).sum = -1 := by
  intro L halt hhead hsum k
  have hsplit : (L.take k).sum + (L.drop k).sum = 0 := by
    rw [← List.sum_append, List.take_append_drop]; exact hsum
  have hpre : (L.take k).sum = 0 ∨ (L.take k).sum = 1 := by
    rw [take_sum_eq_of_alternates L 1 halt hhead k]; split_ifs <;> [left; right] <;> rfl
  rcases hpre with h | h
  · left; omega
  · right; omega

/-- **Prefix-window converse to `take_sum_eq_of_alternates`.** A `±1` list whose
head is `v` and *all of whose nonempty prefix sums lie in `{v, 0}`* is
`Alternates`. This is the converse direction: it manufactures the alternation
structure from a bound on the running sum, the form a non-crossing / Dyck
matching delivers. (The residual after dropping the head flips the window to
`{-v, 0}`, which is why the lemma is parametrized by the head sign `v`.) -/
lemma alternates_of_prefix_window :
    ∀ (L : List ℤ) (v : ℤ), (∀ a ∈ L, a = 1 ∨ a = -1) →
      (L ≠ [] → L.headI = v) →
      (∀ k, 0 < k → k ≤ L.length → (L.take k).sum = v ∨ (L.take k).sum = 0) →
      Alternates L := by
  intro L
  induction L using List.rec with
  | nil => intro v _ _ _; trivial
  | cons a t IH =>
    intro v hpm hhead hpre
    cases t with
    | nil => trivial
    | cons b s =>
      have ha : a = v := by simpa using hhead (by simp)
      subst ha
      have h1 : a = 1 ∨ a = -1 := hpm a (by simp)
      have hsum2 : a + b = a ∨ a + b = 0 := by
        have := hpre 2 (by norm_num) (by simp)
        simpa [List.take, List.sum_cons] using this
      have hb : b = -a := by
        have hbpm : b = 1 ∨ b = -1 := hpm b (by simp)
        rcases h1 with h1 | h1 <;> rcases hbpm with hb' | hb' <;>
          rcases hsum2 with hs | hs <;> omega
      refine ⟨hb, ?_⟩
      apply IH (-a) (fun x hx => hpm x (by simp [hx]))
      · intro _; simp [hb]
      · intro k hk0 hkl
        have hk1 : (a :: b :: s).take (k + 1) = a :: (b :: s).take k := by
          simp
        have hfull := hpre (k + 1) (by omega) (by simp at hkl ⊢; omega)
        rw [hk1, List.sum_cons] at hfull
        rcases hfull with hf | hf
        · right; omega
        · left; omega

end AlternationCore

/-! ### STEP 1 — Curve-order alternation (vertex-side flip; no topology)

At a generic height `y`, assign each vertex `i` the boolean *side*
`side i := y < (vert i).2` ("`vert i` is above `y`"). An edge `i` **spans** `y`
iff its two endpoints lie on opposite sides (`side i ≠ side (i+1)`); when it
spans, it is an **up-edge** (`edgeWind = 1`) iff `vert (i+1)` is above
(`side (i+1) = true`), and a **down-edge** otherwise. The geometric heart of
STEP 1 is then a pure fact about the cyclic boolean sequence `side`: across a
*non-spanning* edge the side is unchanged, so between two consecutive spanning
edges (in cyclic vertex order, with only non-spanning edges in between) the side
is constant — hence the two spanning edges flip *to* opposite sides and therefore
have opposite up/down type. This is `spanning_consecutive_opposite_type` below;
it needs **no** simplicity and **no** topology, only the vertex-height ordering. -/

namespace Pick

open LatticePolygon

namespace LatticePolygon

variable (P : LatticePolygon)

/-- The `y`-side of a vertex: `true` iff the vertex lies strictly above the line
`{·.2 = y}`. The spanning/up/down structure is encoded by this boolean. -/
def vside (y : ℝ) (i : ZMod P.n) : Prop := y < (toReal (P.vert i)).2

/-- The sign of a spanning edge: `+1` for an up-edge (terminal vertex above `y`),
`-1` for a down-edge. -/
noncomputable def edgeSign (y : ℝ) (i : ZMod P.n) : ℤ :=
  if y < (toReal (P.vert (i + 1))).2 then 1 else -1

/-- The threshold (ray-crossing `x`) of edge `i` at height `y`. -/
noncomputable def edgeThr (y : ℝ) (i : ZMod P.n) : ℝ :=
  crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y

/-- The finset of edges spanning height `y` (either orientation). -/
noncomputable def spanningSet (y : ℝ) : Finset (ZMod P.n) :=
  Finset.univ.filter fun i =>
    ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
    ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)

end LatticePolygon

variable (P : LatticePolygon)

/-- An edge **spans** the generic height `y` exactly when its endpoints lie on
opposite sides — the "side flips" characterization of a crossing. -/
lemma spanning_iff_side_ne (y : ℝ) (i : ZMod P.n)
    (hi : (toReal (P.vert i)).2 ≠ y) (hi1 : (toReal (P.vert (i + 1))).2 ≠ y) :
    (((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    ↔ (P.vside y i ≠ P.vside y (i + 1)) := by
  unfold vside
  exact span_iff_above_ne _ _ y hi hi1

/-- **Side is constant across a non-spanning edge.** If edge `i` does not span the
generic height `y`, its two endpoints lie on the same side. The atomic constancy
fact powering the curve-order alternation. -/
lemma side_eq_of_not_spanning (y : ℝ) (i : ZMod P.n)
    (hi : (toReal (P.vert i)).2 ≠ y) (hi1 : (toReal (P.vert (i + 1))).2 ≠ y)
    (hns : ¬(((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))) :
    P.vside y i ↔ P.vside y (i + 1) := by
  rw [spanning_iff_side_ne P y i hi hi1] at hns
  exact iff_of_eq (not_ne_iff.mp hns)

/-- **Type of a spanning edge is determined by the side it flips *to*.** A
spanning edge is an up-edge (`edgeWind = 1` for small `x`) iff its terminal
vertex `vert (i+1)` is above `y`, i.e. iff `vside y (i+1)` holds. -/
lemma spanning_up_iff_side (y : ℝ) (i : ZMod P.n)
    (hi : (toReal (P.vert i)).2 ≠ y) (hi1 : (toReal (P.vert (i + 1))).2 ≠ y)
    (hsp : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2)) :
    (((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)) ↔ P.vside y (i + 1) := by
  unfold vside
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    rcases hsp with hsp | hsp
    · exact hsp
    · exact absurd h (not_lt.mpr (le_of_lt hsp.1))

/-- **Constancy of side across a run of non-spanning edges.** If edges
`i, i+1, …, i+d-1` are all non-spanning at the generic height `y`, then the side
of `vert i` equals the side of `vert (i+d)` — the cumulative version of
`side_eq_of_not_spanning`. (Genericity at every traversed vertex is required.) -/
lemma side_eq_of_run (y : ℝ) (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) :
    ∀ d : ℕ,
      (∀ t : ℕ, t < d → ¬(((toReal (P.vert (i + t))).2 < y ∧
            y < (toReal (P.vert (i + t + 1))).2) ∨
          ((toReal (P.vert (i + t + 1))).2 < y ∧ y < (toReal (P.vert (i + t))).2))) →
      (P.vside y i ↔ P.vside y (i + d)) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d IH =>
    intro hrun
    have hstep : P.vside y (i + (d : ZMod P.n)) ↔ P.vside y ((i + (d : ZMod P.n)) + 1) :=
      side_eq_of_not_spanning P y (i + (d : ZMod P.n)) (hy _) (hy _) (hrun d (by omega))
    have hIH := IH (fun t ht => hrun t (by omega))
    have hcast : (i + ((d : ℕ) + 1 : ℕ) : ZMod P.n) = (i + (d : ZMod P.n)) + 1 := by
      push_cast; ring
    rw [hcast, ← hstep, hIH]

/-- **STEP 1 — Curve-order alternation (consecutive spanning edges have opposite
type).** Fix a generic height `y`. Suppose edge `i` spans `y`, edge `i+d`
(with `d ≥ 1`) spans `y`, and every edge strictly between them in cyclic vertex
order — `i+1, …, i+d-1` — does **not** span. Then the two spanning edges have
**opposite** up/down type: edge `i` is an up-edge iff edge `i+d` is a down-edge.

This is the topology-free combinatorial core of the polygonal Jordan argument:
as the boundary curve is traversed, the side relative to the line `{·.2 = y}`
flips exactly at each crossing and is constant in between, so successive crossings
necessarily reverse orientation. (No `IsSimple` is used; only the cyclic
vertex-height ordering at a generic height.) -/
lemma spanning_consecutive_opposite_type (y : ℝ)
    (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2))
    (hspj : ((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2) ∨
      ((toReal (P.vert (i + d + 1))).2 < y ∧ y < (toReal (P.vert (i + d))).2))
    (hmid : ∀ t : ℕ, 1 ≤ t → t < d →
      ¬(((toReal (P.vert (i + t))).2 < y ∧ y < (toReal (P.vert (i + t + 1))).2) ∨
        ((toReal (P.vert (i + t + 1))).2 < y ∧ y < (toReal (P.vert (i + t))).2))) :
    (((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2)) ↔
      ¬(((toReal (P.vert (i + d))).2 < y ∧ y < (toReal (P.vert (i + d + 1))).2)) := by
  -- Work with `j := i + d`.  The run `i+1, …, i+(d-1)` of non-spanning edges keeps
  -- the side constant, so `side (i+1) ↔ side j`.
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hrun : P.vside y (i + 1) ↔ P.vside y (i + (((e : ℕ) + 1 : ℕ) : ZMod P.n)) := by
    have h := side_eq_of_run P y hy (i + 1) e (fun t ht => by
      have h := hmid (t + 1) (by omega) (by omega)
      rw [show (i + (↑(t + 1) : ZMod P.n)) = i + 1 + (↑t : ZMod P.n) by push_cast; ring] at h
      exact h)
    have hcast : (i + 1) + (e : ZMod P.n) = i + (((e : ℕ) + 1 : ℕ) : ZMod P.n) := by
      push_cast; ring
    rw [hcast] at h; exact h
  set j : ZMod P.n := i + (((e : ℕ) + 1 : ℕ) : ZMod P.n) with hj_def
  -- Edge `i` is up iff `side (i+1)`; edge `j` is up iff `side (j+1)`.
  have hi := spanning_up_iff_side P y i (hy i) (hy (i + 1)) hspi
  have hjup := spanning_up_iff_side P y j (hy j) (hy (j + 1)) hspj
  -- Edge `j` spans, so its side flips: `side j ≠ side (j+1)`.
  have hflip : P.vside y j ≠ P.vside y (j + 1) :=
    (spanning_iff_side_ne P y j (hy j) (hy (j + 1))).mp hspj
  -- The goal is already in `j`-form; assemble propositionally.
  rw [hi, hjup, hrun]
  -- Now: `side j ↔ ¬ side (j+1)`, given `side j ≠ side (j+1)`.
  constructor
  · intro h hc; exact hflip (by rw [eq_iff_iff]; exact ⟨fun _ => hc, fun _ => h⟩)
  · intro h
    by_contra hc
    exact hflip (by rw [eq_iff_iff]; exact ⟨fun hjj => absurd hjj hc, fun hj1 => absurd hj1 h⟩)

/-- **`edgeSign`-form of `spanning_consecutive_opposite_type`.** Two cyclically
consecutive spanning edges (`i` and `i+d`, with only non-spanning edges strictly
between) carry *opposite* signs. -/
lemma edgeSign_consecutive_opposite (y : ℝ)
    (hy : ∀ k, (toReal (P.vert k)).2 ≠ y) (i : ZMod P.n) (d : ℕ) (hd : 1 ≤ d)
    (hspi : i ∈ P.spanningSet y) (hspj : i + (d : ZMod P.n) ∈ P.spanningSet y)
    (hmid : ∀ t : ℕ, 1 ≤ t → t < d → (i + (t : ZMod P.n)) ∉ P.spanningSet y) :
    P.edgeSign y i = - P.edgeSign y (i + (d : ZMod P.n)) := by
  classical
  simp only [spanningSet, Finset.mem_filter, Finset.mem_univ, true_and] at hspi hspj hmid
  have hspj' : ((toReal (P.vert (i + (d:ZMod P.n)))).2 < y ∧
        y < (toReal (P.vert (i + (d:ZMod P.n) + 1))).2) ∨
      ((toReal (P.vert (i + (d:ZMod P.n) + 1))).2 < y ∧
        y < (toReal (P.vert (i + (d:ZMod P.n)))).2) := hspj
  have hkey := spanning_consecutive_opposite_type P y hy i d hd hspi hspj'
    (fun t ht1 ht2 => hmid t ht1 ht2)
  -- `edgeSign y i = 1 ↔ i is an up-edge ↔ left side of hkey`
  have hi_up : P.edgeSign y i = 1 ↔
      (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2 := by
    unfold edgeSign
    constructor
    · intro h
      have hpos : y < (toReal (P.vert (i + 1))).2 := by
        by_contra hc; rw [if_neg hc] at h; norm_num at h
      rcases hspi with hu | hd'
      · exact hu
      · exact absurd hpos (not_lt.mpr (le_of_lt hd'.1))
    · rintro ⟨_, h2⟩; rw [if_pos h2]
  have hj_up : P.edgeSign y (i + (d:ZMod P.n)) = 1 ↔
      (toReal (P.vert (i + (d:ZMod P.n)))).2 < y ∧
        y < (toReal (P.vert (i + (d:ZMod P.n) + 1))).2 := by
    unfold edgeSign
    constructor
    · intro h
      have hpos : y < (toReal (P.vert (i + (d:ZMod P.n) + 1))).2 := by
        by_contra hc; rw [if_neg hc] at h; norm_num at h
      rcases hspj' with hu | hd'
      · exact hu
      · exact absurd hpos (not_lt.mpr (le_of_lt hd'.1))
    · rintro ⟨_, h2⟩; rw [if_pos h2]
  have hisign : P.edgeSign y i = 1 ∨ P.edgeSign y i = -1 := by
    unfold edgeSign; split_ifs <;> simp
  have hjsign : P.edgeSign y (i + (d:ZMod P.n)) = 1 ∨
      P.edgeSign y (i + (d:ZMod P.n)) = -1 := by
    unfold edgeSign; split_ifs <;> simp
  rcases hisign with hi1 | hi1 <;> rcases hjsign with hj1 | hj1
  · -- both +1: i up, j up; but hkey says i up ↔ ¬ j up
    exfalso
    have hiu := hi_up.mp hi1
    have hju := hj_up.mp hj1
    exact (hkey.mp hiu) hju
  · rw [hi1, hj1]; norm_num
  · rw [hi1, hj1]
  · -- both -1: i not up, j not up; hkey: i up ↔ ¬(j's up-condition)
    exfalso
    have hinu : ¬ ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) := by
      intro h; rw [← hi_up] at h; rw [h] at hi1; norm_num at hi1
    have hjnu : ¬ ((toReal (P.vert (i + (d:ZMod P.n)))).2 < y ∧
        y < (toReal (P.vert (i + (d:ZMod P.n) + 1))).2) := by
      intro h; rw [← hj_up] at h; rw [h] at hj1; norm_num at hj1
    exact hinu (hkey.mpr hjnu)

/-! ### STEP 4 — Wiring the count inequalities to the dichotomy (conditional)

The count inequalities `#down ≤ #up ≤ #down + 1` consumed by
`winding_ae_mem_zero_one_of_count` are equivalent, by
`winding = #up − #down` (`winding_eq_upCount_sub_downCount`), to the bound
`0 ≤ winding (x,y) ≤ 1` at the swept point. STEP 1–3 supply exactly this bound at
generic heights (the x-sorted alternation is `±1`-alternating with head `−1`, so
its suffix sums — the running winding count, swept right-to-left — lie in `{0,1}`
by `AlternationCore.prefixSums_mem_neg`). The lemmas here perform the **purely
mechanical** transfer in both directions, isolating the single remaining
*geometric* gap to the hypothesis `winding_bdd` below: *at every generic point the
winding is between `0` and `1`.* -/

/-- **Generic winding-bound ⇒ count inequalities.** At a generic height, the bound
`0 ≤ winding (x,y) ≤ 1` is *definitionally* the pair of count inequalities
`#up ≤ #down + 1` and `#down ≤ #up`, since `winding = #up − #down`. This is the
exact hypothesis shape required by `winding_ae_mem_zero_one_of_count`. -/
lemma count_ineqs_of_winding_bdd (x y : ℝ)
    (h0 : 0 ≤ P.winding (x, y)) (h1 : P.winding (x, y) ≤ 1) :
    ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card
        ≤ (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card + 1) ∧
      ((Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = -1).card
        ≤ (Finset.univ.filter fun i =>
          edgeWind (toReal (P.vert i)) (toReal (P.vert (i + 1))) (x, y) = 1).card) := by
  rw [winding_eq_upCount_sub_downCount] at h0 h1
  omega

/-- **STEP 4 (mechanical) — generic winding-bound ⇒ a.e. dichotomy.** If at every
generic height (no vertex at that height) the swept winding satisfies
`0 ≤ winding (x,y) ≤ 1`, then `winding ∈ {0,1}` almost everywhere. This is the
clean bridge consuming the STEP 1–3 output: the *only* remaining geometric input
is `winding_bdd`, which is exactly what the curve-order alternation
(`spanning_consecutive_opposite_type`), its x-order transfer, and positive
orientation deliver via `AlternationCore.prefixSums_mem_neg`. -/
lemma winding_ae_mem_zero_one_of_winding_bdd
    (winding_bdd : ∀ x y : ℝ, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1) :
    ∀ᵐ q : ℝ × ℝ, P.winding q = 0 ∨ P.winding q = 1 := by
  apply Pick.winding_ae_mem_zero_one_of_count
  intro x y hgen
  obtain ⟨h0, h1⟩ := winding_bdd x y hgen
  exact count_ineqs_of_winding_bdd P x y h0 h1

/-! ### STEP A — Plumbing: winding-bound from an x-sorted alternating sign list

We isolate the whole remaining geometric content into a single hypothesis:
*the spanning edges, listed in increasing order of their crossing threshold,
have signs forming an `Alternates` list with head `-1`.* From this the bound
`0 ≤ winding (x,y) ≤ 1` is purely mechanical.

The bridge: `winding (x,y)` equals the sum of the signs of the spanning edges
whose threshold is `> x`. Listing the signs in increasing threshold order as
`L`, this is the *suffix* of `L` past the `k` thresholds that are `≤ x`. Since
`L` alternates from `-1` its total sum is `0` (even length: up/down counts are
equal), so each suffix sum `= -(prefix sum) ∈ {0,1}` by `prefixSums_mem_neg`. -/

/-- **Filter of a sorted list by an up-closed predicate is a `dropWhile`.** If `L`
is `R`-sorted and `p` is up-closed under `R` (so once `p` holds it holds onward),
then `L.filter p = L.dropWhile (fun a => !p a)`. -/
lemma filter_eq_dropWhile_of_sorted {α : Type*} (R : α → α → Prop) (p : α → Bool) :
    ∀ (L : List α), L.Pairwise R → (∀ a b, R a b → p a → p b) →
      L.filter p = L.dropWhile (fun a => !p a) := by
  intro L
  induction L with
  | nil => intro _ _; rfl
  | cons a t IH =>
    intro hpw hclosed
    rw [List.pairwise_cons] at hpw
    by_cases hpa : p a
    · -- every element of `a :: t` has `p`, so both sides are `a :: t`
      have hall : ∀ b ∈ (a :: t), p b := by
        intro b hb
        rcases List.mem_cons.mp hb with h | h
        · subst h; exact hpa
        · exact hclosed a b (hpw.1 b h) hpa
      rw [List.filter_eq_self.mpr hall,
        List.dropWhile_eq_self_iff.mpr (fun _ => by simp [hpa])]
    · rw [List.filter_cons_of_neg (by simp [hpa]),
        List.dropWhile_cons_of_pos (by simp [hpa])]
      exact IH hpw.2 hclosed

/-- **The signs of the spanning edges sum to `0`.** Up- and down-crossings are
equinumerous (`card_up_eq_card_down`), and `edgeSign` is `+1` on up-spanning,
`-1` on down-spanning edges. -/
lemma sum_edgeSign_spanning_eq_zero (y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    ∑ i ∈ P.spanningSet y, P.edgeSign y i = 0 := by
  classical
  unfold spanningSet edgeSign
  rw [Finset.sum_filter]
  have per : ∀ i,
      (if ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
          ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) then
        (if y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else -1) else 0)
      = (if (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2 then (1 : ℤ) else 0)
        - (if (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2 then 1 else 0) := by
    intro i
    have ha := hy i
    have hb := hy (i + 1)
    by_cases hup : (toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2
    · rw [if_pos (Or.inl hup), if_pos hup.2, if_pos ⟨le_of_lt hup.1, hup.2⟩,
        if_neg (fun h => absurd h.1 (not_le.mpr hup.2))]; ring
    · by_cases hdn : (toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2
      · rw [if_pos (Or.inr hdn), if_neg (not_lt.mpr (le_of_lt hdn.1)),
          if_neg (fun h => absurd h.1 (not_le.mpr hdn.2)),
          if_pos ⟨le_of_lt hdn.1, hdn.2⟩]; ring
      · rw [if_neg (by tauto)]
        rw [if_neg (fun h => hup ⟨lt_of_le_of_ne h.1 ha, h.2⟩),
          if_neg (fun h => hdn ⟨lt_of_le_of_ne h.1 hb, h.2⟩)]
        ring
  rw [Finset.sum_congr rfl fun i _ => per i, Finset.sum_sub_distrib]
  have e1 : (∑ i, if (toReal (P.vert i)).2 ≤ y ∧ y < (toReal (P.vert (i + 1))).2 then (1:ℤ) else 0)
      = ((Finset.univ.filter fun i => (toReal (P.vert i)).2 ≤ y ∧
          y < (toReal (P.vert (i + 1))).2).card : ℤ) := by
    rw [Finset.card_filter]; push_cast; rfl
  have e2 : (∑ i, if (toReal (P.vert (i + 1))).2 ≤ y ∧ y < (toReal (P.vert i)).2 then (1:ℤ) else 0)
      = ((Finset.univ.filter fun i => (toReal (P.vert (i + 1))).2 ≤ y ∧
          y < (toReal (P.vert i)).2).card : ℤ) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [e1, e2, card_up_eq_card_down P y, sub_self]

/-- `edgeSign` is always `±1` (it is defined by a single `if`). -/
lemma edgeSign_eq_one_or_neg_one (y : ℝ) (i : ZMod P.n) :
    P.edgeSign y i = 1 ∨ P.edgeSign y i = -1 := by
  unfold edgeSign; split_ifs <;> simp

/-- **#2 — the spanning-edge signs sum to zero** (named alias of
`sum_edgeSign_spanning_eq_zero`, the form the alternation packaging consumes). -/
lemma edgeSign_sum_zero (y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    ∑ i ∈ P.spanningSet y, P.edgeSign y i = 0 :=
  sum_edgeSign_spanning_eq_zero P y hy

/-- **#2 (corollary) — up- and down-spanning edges are equinumerous.** Since the
spanning signs are `±1` and sum to `0`, exactly half are `+1`: the count of
up-spanning edges (`edgeSign = 1`) equals the count of down-spanning edges
(`edgeSign = -1`). In particular the spanning set has even cardinality. This is
the equal-count fact the non-crossing alternation argument relies on. -/
lemma edgeSign_card_pos_eq_card_neg (y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    ((P.spanningSet y).filter (fun i => P.edgeSign y i = 1)).card
      = ((P.spanningSet y).filter (fun i => P.edgeSign y i = -1)).card := by
  classical
  set s := P.spanningSet y with hs
  set g := P.edgeSign y with hg
  have hsplit : s = s.filter (fun i => g i = 1) ∪ s.filter (fun i => g i = -1) := by
    ext i; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hi; rcases edgeSign_eq_one_or_neg_one P y i with h | h <;>
        [exact Or.inl ⟨hi, h⟩; exact Or.inr ⟨hi, h⟩]
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hdisj : Disjoint (s.filter (fun i => g i = 1)) (s.filter (fun i => g i = -1)) := by
    rw [Finset.disjoint_filter]; intro i _ h1; rw [h1]; decide
  have hsum2 : ∑ i ∈ s, g i = 0 := edgeSign_sum_zero P y hy
  rw [hsplit, Finset.sum_union hdisj] at hsum2
  rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2),
      Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)] at hsum2
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg] at hsum2
  have : ((s.filter (fun i => g i = 1)).card : ℤ) = (s.filter (fun i => g i = -1)).card := by
    omega
  exact_mod_cast this

/-- **#1 — the spanning edges enumerate as a threshold-sorted `Nodup` list.** At a
generic height `y`, the edges spanning `y` can be listed (without repetition) in
**strictly** increasing order of their crossing threshold `edgeThr y`. The strict
order requires simplicity: distinct spanning edges have distinct thresholds
(`crossThreshold_ne_distinct_spanning`), which upgrades the `≤`-sorted insertion
order to a strict `<`-pairwise list. This is the `L` consumed throughout STEP A. -/
lemma spanning_threshold_nodup_sorted (hP : P.IsSimple) (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    ∃ L : List (ZMod P.n), L.Nodup ∧ (∀ i, i ∈ L ↔ i ∈ P.spanningSet y) ∧
      L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j) := by
  classical
  set f : ZMod P.n → ℝ := fun i => P.edgeThr y i with hf
  let r : ZMod P.n → ZMod P.n → Prop := fun i j => f i ≤ f j
  haveI : DecidableRel r := fun i j => inferInstanceAs (Decidable (f i ≤ f j))
  haveI : IsTrans (ZMod P.n) r := ⟨fun a b c hab hbc => le_trans hab hbc⟩
  haveI : Std.Total r := ⟨fun a b => le_total (f a) (f b)⟩
  set L := List.insertionSort r (P.spanningSet y).toList with hL
  have hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y := by
    intro i; rw [hL, List.mem_insertionSort, Finset.mem_toList]
  have hnd : L.Nodup :=
    (List.perm_insertionSort r _).nodup_iff.mpr (P.spanningSet y).nodup_toList
  refine ⟨L, hnd, hmem, ?_⟩
  -- distinctness of thresholds on the spanning set (needs simplicity)
  have hdist : ∀ a ∈ P.spanningSet y, ∀ b ∈ P.spanningSet y, a ≠ b → f a ≠ f b := by
    intro a ha b hb hab
    simp only [spanningSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact crossThreshold_ne_distinct_spanning P hP y hy a b hab ha hb
  -- combine `≤`-sorted with `Nodup` (giving `≠`) to get strict `<`-sorted
  have hpw : L.Pairwise r := List.pairwise_insertionSort r _
  have hcomb : L.Pairwise (fun a b => r a b ∧ a ≠ b) := by
    rw [List.pairwise_and_iff]; exact ⟨hpw, hnd⟩
  refine hcomb.imp_of_mem ?_
  intro a b ha hb hab
  obtain ⟨hle, hne'⟩ := hab
  exact lt_of_le_of_ne hle (hdist a ((hmem a).mp ha) b ((hmem b).mp hb) hne')

/-- **Winding as a sum over spanning edges.** At a generic height, the winding at
`(x,y)` is the sum of signs of the spanning edges whose threshold exceeds `x`. -/
lemma winding_eq_sum_spanning (x y : ℝ) (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) :
    P.winding (x, y)
      = ∑ i ∈ (P.spanningSet y).filter (fun i => x < P.edgeThr y i), P.edgeSign y i := by
  classical
  rw [winding_generic_sum P x y hy]
  unfold spanningSet edgeSign edgeThr
  rw [Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hsp : ((toReal (P.vert i)).2 < y ∧ y < (toReal (P.vert (i + 1))).2) ∨
      ((toReal (P.vert (i + 1))).2 < y ∧ y < (toReal (P.vert i)).2) <;>
    by_cases hx : x < crossThreshold (toReal (P.vert i)) (toReal (P.vert (i + 1))) y <;>
    simp only [hsp, hx, true_and, false_and, and_true, and_false, if_true, if_false,
      mul_one, mul_zero] <;>
    simp_all

/-- **STEP A — the winding bound from an x-sorted alternating sign list.** Suppose
the spanning edges at the generic height `y` are enumerated, in strictly increasing
order of their crossing threshold, by a `Nodup` list `L`; and the corresponding
sign list `L.map (edgeSign y)` alternates and (if nonempty) starts with `-1`. Then
at every `x`, `0 ≤ winding (x,y) ≤ 1`. This isolates the entire remaining geometric
gap to producing the alternating x-sorted list. -/
lemma winding_bdd_of_xsorted_alternates (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n))
    (hnodup : L.Nodup) (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (halt : AlternationCore.Alternates (L.map (P.edgeSign y)))
    (hhead : L.map (P.edgeSign y) ≠ [] → (L.map (P.edgeSign y)).headI = -1)
    (x : ℝ) : 0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1 := by
  classical
  -- The filter predicate (Bool) selecting thresholds to the right of `x`.
  set p : ZMod P.n → Bool := fun i => decide (x < P.edgeThr y i) with hp
  -- `winding (x,y)` is the sum of signs over spanning edges with threshold `> x`.
  have hw : P.winding (x, y) = ((L.filter p).map (P.edgeSign y)).sum := by
    rw [winding_eq_sum_spanning P x y hy]
    rw [show (P.spanningSet y).filter (fun i => x < P.edgeThr y i)
        = (L.filter p).toFinset by
      rw [List.toFinset_filter]
      ext i
      simp only [Finset.mem_filter, List.mem_toFinset, hmem i, hp, decide_eq_true_eq]]
    rw [List.sum_toFinset _ (hnodup.filter p)]
  -- The filter of a threshold-sorted list is a `dropWhile`, hence a `drop`.
  have hfilter : L.filter p = L.dropWhile (fun i => !p i) :=
    filter_eq_dropWhile_of_sorted _ p L hsorted
      (fun a b hab hpa => by
        simp only [hp, decide_eq_true_eq] at hpa ⊢; exact lt_trans hpa hab)
  -- `dropWhile q L = drop k L`, so its sign-sum is a suffix sum of `L.map edgeSign`.
  set q : ZMod P.n → Bool := fun i => !p i with hq
  have hdrop : (L.dropWhile q).map (P.edgeSign y)
      = (L.map (P.edgeSign y)).drop (L.takeWhile q).length := by
    have hsplit : L.map (P.edgeSign y)
        = (L.takeWhile q).map (P.edgeSign y) ++ (L.dropWhile q).map (P.edgeSign y) := by
      rw [← List.map_append, List.takeWhile_append_dropWhile]
    rw [hsplit, ← List.length_map (P.edgeSign y), List.drop_left]
  -- The total sign sum is `0` (up/down counts equal).
  have htot : (L.map (P.edgeSign y)).sum = 0 := by
    rw [← List.sum_toFinset _ hnodup,
      show L.toFinset = P.spanningSet y by ext i; rw [List.mem_toFinset, hmem i]]
    exact sum_edgeSign_spanning_eq_zero P y hy
  rw [hw, hfilter, hdrop]
  rcases AlternationCore.suffixSums_mem _ halt hhead htot (L.takeWhile q).length with h | h <;>
    rw [h] <;> omega

/-- **Suffix-as-filter for a threshold-sorted list.** For a list `L` strictly
sorted by `f` and any `k ≤ L.length`, there is a threshold `x` so that the elements
of `L` with `f > x` are exactly `L.drop k` (the `k`-th suffix). For `k = 0` pick
`x` below the minimum; for the inductive step take `x = max x₀ (f a)`, dropping the
head while keeping the tail's filter unchanged (every retained tail element has
`f > f a`). This converts a *suffix sum* of the sign list into a single winding
value `winding (x,y)` — the bridge from `winding_eq_sum_spanning` to the prefix
window. -/
lemma exists_x_drop_of_sorted {α : Type*} (f : α → ℝ) (L : List α)
    (hsorted : L.Pairwise (fun i j => f i < f j)) :
    ∀ k : ℕ, k ≤ L.length →
      ∃ x : ℝ, L.filter (fun i => decide (x < f i)) = L.drop k := by
  induction L with
  | nil => intro k hk; exact ⟨0, by simp⟩
  | cons a t IH =>
    rw [List.pairwise_cons] at hsorted
    obtain ⟨hahead, htail⟩ := hsorted
    intro k hk
    cases k with
    | zero =>
      refine ⟨f a - 1, ?_⟩
      rw [List.drop_zero]; apply List.filter_eq_self.mpr; intro i hi
      rcases List.mem_cons.mp hi with h | h
      · subst h; simp
      · simp only [decide_eq_true_eq]; have := hahead i h; linarith
    | succ m =>
      have hkt : m ≤ t.length := by simpa using hk
      obtain ⟨x₀, hx₀⟩ := IH htail m hkt
      refine ⟨max x₀ (f a), ?_⟩
      rw [List.drop_succ_cons, List.filter_cons]
      have hdrop_a : ¬ (max x₀ (f a) < f a) := by simp
      rw [decide_eq_false (by simpa using hdrop_a)]
      rw [← hx₀]
      apply List.filter_congr
      intro i hi
      have hai := hahead i hi
      simp only [decide_eq_decide]
      constructor
      · intro h; exact lt_of_le_of_lt (le_max_left _ _) h
      · intro h; exact max_lt h hai

/-- **Mirror of STEP A (head `+1`).** With the same x-sorted alternating setup but
head `+1`, the winding satisfies `-1 ≤ winding (x,y) ≤ 0` at every `x`. Used to
derive the sign of the head from positive orientation: head `+1` would force
`winding ≤ 0` everywhere, contradicting positive area. -/
lemma winding_nonpos_of_xsorted_alternates (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n))
    (hnodup : L.Nodup) (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (halt : AlternationCore.Alternates (L.map (P.edgeSign y)))
    (hhead : L.map (P.edgeSign y) ≠ [] → (L.map (P.edgeSign y)).headI = 1)
    (x : ℝ) : -1 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 0 := by
  classical
  set p : ZMod P.n → Bool := fun i => decide (x < P.edgeThr y i) with hp
  have hw : P.winding (x, y) = ((L.filter p).map (P.edgeSign y)).sum := by
    rw [winding_eq_sum_spanning P x y hy]
    rw [show (P.spanningSet y).filter (fun i => x < P.edgeThr y i)
        = (L.filter p).toFinset by
      rw [List.toFinset_filter]
      ext i
      simp only [Finset.mem_filter, List.mem_toFinset, hmem i, hp, decide_eq_true_eq]]
    rw [List.sum_toFinset _ (hnodup.filter p)]
  have hfilter : L.filter p = L.dropWhile (fun i => !p i) :=
    filter_eq_dropWhile_of_sorted _ p L hsorted
      (fun a b hab hpa => by
        simp only [hp, decide_eq_true_eq] at hpa ⊢; exact lt_trans hpa hab)
  set q : ZMod P.n → Bool := fun i => !p i with hq
  have hdrop : (L.dropWhile q).map (P.edgeSign y)
      = (L.map (P.edgeSign y)).drop (L.takeWhile q).length := by
    have hsplit : L.map (P.edgeSign y)
        = (L.takeWhile q).map (P.edgeSign y) ++ (L.dropWhile q).map (P.edgeSign y) := by
      rw [← List.map_append, List.takeWhile_append_dropWhile]
    rw [hsplit, ← List.length_map (P.edgeSign y), List.drop_left]
  have htot : (L.map (P.edgeSign y)).sum = 0 := by
    rw [← List.sum_toFinset _ hnodup,
      show L.toFinset = P.spanningSet y by ext i; rw [List.mem_toFinset, hmem i]]
    exact sum_edgeSign_spanning_eq_zero P y hy
  rw [hw, hfilter, hdrop]
  rcases AlternationCore.suffixSums_mem_nonpos _ halt hhead htot (L.takeWhile q).length with h | h <;>
    rw [h] <;> omega

/-! ### STEP B — Sign of the head from orientation

`edgeSign` is always `±1`, so the head of a nonempty sorted sign list is `+1` or
`-1`. The mirror bound shows: if the head were `+1`, the winding would be `≤ 0`
*everywhere* on the line `{·.2 = y}`. So as soon as the winding is *positive*
anywhere on that line, the head must be `-1`. Positive orientation supplies such a
positive value (via `∫∫ winding = shoelace > 0`), pinning the head to `-1`. -/

/-- The head of the (nonempty) x-sorted sign list is `±1` (`edgeSign` is `±1`). -/
lemma headI_edgeSign_eq (y : ℝ) (L : List (ZMod P.n))
    (hne : L.map (P.edgeSign y) ≠ []) :
    (L.map (P.edgeSign y)).headI = 1 ∨ (L.map (P.edgeSign y)).headI = -1 := by
  cases L with
  | nil => simp at hne
  | cons a t =>
    simp only [List.map_cons, List.headI_cons]
    unfold edgeSign
    split_ifs <;> simp

/-- **STEP B — the head is `-1` once the winding is positive somewhere on the line.**
For an x-sorted alternating sign list at generic height `y`, if `winding (x₀,y) > 0`
for some `x₀`, then the sign list (if nonempty) starts with `-1` (a down-edge is
the leftmost crossing). Otherwise the mirror bound would force `winding ≤ 0`. -/
lemma head_neg_of_winding_pos (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n))
    (hnodup : L.Nodup) (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (halt : AlternationCore.Alternates (L.map (P.edgeSign y)))
    (x₀ : ℝ) (hpos : 0 < P.winding (x₀, y)) :
    L.map (P.edgeSign y) ≠ [] → (L.map (P.edgeSign y)).headI = -1 := by
  intro hne
  rcases headI_edgeSign_eq P y L hne with hhead | hhead
  · -- head = +1 would force winding ≤ 0 at x₀, contradiction
    exfalso
    have := (winding_nonpos_of_xsorted_alternates P y hy L hnodup hmem hsorted halt
      (fun _ => hhead) x₀).2
    linarith
  · exact hhead

/-- **Winding is a realized suffix sum.** For the threshold-sorted `Nodup` spanning
list `L` and any `k ≤ L.length`, there is an `x` at which `winding (x,y)` equals the
`k`-th suffix sum of the sign list `L.map (edgeSign y)`. The bridge from
`winding_eq_sum_spanning` (winding = sum of signs with threshold `> x`) and
`exists_x_drop_of_sorted` (a threshold realizing the suffix). -/
lemma exists_x_winding_eq_drop_sum (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n)) (hnodup : L.Nodup)
    (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (k : ℕ) (hk : k ≤ L.length) :
    ∃ x : ℝ, P.winding (x, y) = ((L.map (P.edgeSign y)).drop k).sum := by
  classical
  obtain ⟨x, hx⟩ := exists_x_drop_of_sorted (P.edgeThr y) L hsorted k hk
  refine ⟨x, ?_⟩
  rw [winding_eq_sum_spanning P x y hy]
  rw [show (P.spanningSet y).filter (fun i => x < P.edgeThr y i)
      = (L.filter (fun i => decide (x < P.edgeThr y i))).toFinset by
    rw [List.toFinset_filter]; ext i
    simp only [Finset.mem_filter, List.mem_toFinset, hmem i, decide_eq_true_eq]]
  rw [List.sum_toFinset _ (hnodup.filter _), hx, List.map_drop]

/-- **STEP C reduction — the x-sorted alternation `halt` from the winding bound.**
This is the *converse* of `winding_bdd_of_xsorted_alternates`: it manufactures the
alternating sign list `halt` (input **C**) *from* the topological winding bound
`0 ≤ winding ≤ 1` at every generic point, together with positivity somewhere on the
line. The mechanism: every prefix sum of the sign list equals `−winding (x,y)` for a
realized `x` (since the total sign sum is `0`, prefix `= −`suffix `= −winding`); the
bound pins each prefix sum to `{0, −1}`, which (with head `−1`) is exactly the
`alternates_of_prefix_window` hypothesis. Thus the *only* remaining geometric input
to the whole STEP A–C pipeline is the winding bound `winding ≤ 1` (`winding ≥ 0` is
free, coming out of the same alternation). -/
lemma alternates_of_winding_bdd (y : ℝ)
    (hy : ∀ i, (toReal (P.vert i)).2 ≠ y) (L : List (ZMod P.n)) (hnodup : L.Nodup)
    (hmem : ∀ i, i ∈ L ↔ i ∈ P.spanningSet y)
    (hsorted : L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j))
    (hbdd : ∀ x : ℝ, 0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1)
    (x₀ : ℝ) (hpos : 0 < P.winding (x₀, y)) :
    AlternationCore.Alternates (L.map (P.edgeSign y)) := by
  classical
  set S := L.map (P.edgeSign y) with hS
  -- total sign sum is zero
  have htot : S.sum = 0 := by
    rw [hS, ← List.sum_toFinset _ hnodup,
      show L.toFinset = P.spanningSet y by ext i; rw [List.mem_toFinset, hmem i]]
    exact sum_edgeSign_spanning_eq_zero P y hy
  -- the head is `-1` (down-edge leftmost), from positivity
  have hpm : ∀ a ∈ S, a = 1 ∨ a = -1 := by
    intro a ha
    rw [hS, List.mem_map] at ha
    obtain ⟨i, _, rfl⟩ := ha
    unfold edgeSign; split_ifs <;> simp
  by_cases hSne : S = []
  · rw [hSne]; trivial
  have hSne' : S ≠ [] := hSne
  have hlen : 1 ≤ L.length := by
    rcases L with _ | _ <;> simp_all
  have hhead : S.headI = -1 := by
    rcases headI_edgeSign_eq P y L hSne' with h1 | h1
    · -- head `+1` ⟹ winding(x,y) = (S.drop 1).sum = -S.headI = -1, contra `0 ≤ winding`.
      exfalso
      obtain ⟨x, hx⟩ := exists_x_winding_eq_drop_sum P y hy L hnodup hmem hsorted 1 hlen
      rw [← hS] at hx
      have hdrop1 : (S.drop 1).sum = S.sum - S.headI := by
        cases hSc : S with
        | nil => rw [hSc] at hSne'; simp at hSne'
        | cons b s => simp [List.headI]
      have hwx : P.winding (x, y) = -1 := by
        rw [hx, hdrop1, htot]
        rw [show S.headI = (1 : ℤ) by rw [hS]; exact h1]; ring
      have := (hbdd x).1
      rw [hwx] at this; norm_num at this
    · exact h1
  -- prefix-window: every nonempty prefix sum is `-1` or `0`
  apply AlternationCore.alternates_of_prefix_window S (-1) hpm (fun _ => hhead)
  intro k hk0 hkl
  -- (S.take k).sum = S.sum - (S.drop k).sum = -(S.drop k).sum = -winding(x,y)
  have hsplit : (S.take k).sum + (S.drop k).sum = 0 := by
    rw [← List.sum_append, List.take_append_drop]; exact htot
  obtain ⟨x, hx⟩ := exists_x_winding_eq_drop_sum P y hy L hnodup hmem hsorted k
    (by have : k ≤ S.length := hkl; rw [hS, List.length_map] at this; exact this)
  rw [← hS] at hx
  obtain ⟨h0, h1⟩ := hbdd x
  rw [← hx] at hsplit
  -- winding ∈ {0,1}; (take).sum = -winding ∈ {0,-1}
  rcases (by omega : P.winding (x, y) = 0 ∨ P.winding (x, y) = 1) with hw | hw
  · right; omega
  · left; omega

/-- **STEP C capstone — the alternation hypothesis `halt` from the winding bound.**
For a *simple* polygon, the alternating x-sorted spanning list (`halt`, input **C**
of `winding_bdd_of_alternation_and_pos`) is produced at every generic height `y`
from two inputs:
* the topological **winding bound** `0 ≤ winding (x,y) ≤ 1` at every generic point
  (the no-nesting / `winding_le_one` crux), and
* **positivity** of the winding somewhere on each spanning line (input **B'**,
  delivered by positive orientation).

This is the converse plumbing of `winding_bdd_of_alternation_and_pos`: the two
together show `halt ⟺ winding_bdd` at every height, so the *entire* remaining
geometric content of the general-`n` `h01` is the single topological inequality
`winding (x,y) ≤ 1` (with `winding ≥ 0` falling out of the same alternation). The
threshold-sorted `Nodup` list is `spanning_threshold_nodup_sorted`; the alternation
is `alternates_of_winding_bdd`. -/
lemma halt_of_winding_bdd (hP : P.IsSimple)
    (hbdd : ∀ x y : ℝ, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1)
    (hposline : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y)) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      ∃ L : List (ZMod P.n), L.Nodup ∧ (∀ i, i ∈ L ↔ i ∈ P.spanningSet y) ∧
        L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j) ∧
        AlternationCore.Alternates (L.map (P.edgeSign y)) := by
  intro y hy
  obtain ⟨L, hnodup, hmem, hsorted⟩ := spanning_threshold_nodup_sorted P hP y hy
  refine ⟨L, hnodup, hmem, hsorted, ?_⟩
  -- If there are no spanning edges, the list is empty and `Alternates` is trivial.
  by_cases hSne : (P.spanningSet y).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hposline y hy hSne
    exact alternates_of_winding_bdd P y hy L hnodup hmem hsorted
      (fun x => hbdd x y hy) x₀ hx₀
  · have hLnil : L = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro i hi
      exact hSne ⟨i, (hmem i).mp hi⟩
    rw [hLnil]; simp [AlternationCore.Alternates]

/-- **`hposline` from cross-section positivity (general `n`).** A positive
cross-section value `0 < ∫ x, winding (x,y) dx` at a height `y` forces the winding
to be strictly positive at *some* `x₀` on that line — otherwise the integrand
would be `≤ 0` everywhere and the integral `≤ 0`. This is the *trivial half* of
`hposline`: it reduces the geometric input **B'** entirely to the analytic claim
`0 < c(y)` at every generic spanning height. The remaining (genuinely hard, and
the only outstanding gap for **B'**) content is `crossSection_pos_at_spanning`
below — for triangles this is `crossSection_pos_on_band`; for general `n` it is
the band-propagation of the single positive height `crossSection_pos_somewhere_generic`
across vertex events, which needs `crossSection_ne_zero` for general `n`. -/
lemma exists_winding_pos_of_crossSection_pos (y : ℝ)
    (hc : 0 < ∫ x, (P.winding (x, y) : ℝ)) :
    ∃ x₀, 0 < P.winding (x₀, y) := by
  by_contra h
  push_neg at h
  have hle : ∀ x, (P.winding (x, y) : ℝ) ≤ 0 := fun x => by exact_mod_cast h x
  have := MeasureTheory.integral_nonpos (μ := MeasureTheory.volume) hle
  linarith

/-- **`hposline` reduced to cross-section positivity.** Given that the cross-section
value is positive at every generic spanning height, the positivity input **B'**
(`hposline`) for `winding_bdd_of_alternation_and_pos` holds. This packages the
trivial reduction `exists_winding_pos_of_crossSection_pos` against the `spanningSet`
nonemptiness so the only remaining obligation is `0 < c(y)` (the analytic gap). -/
lemma hposline_of_crossSection_pos
    (hcpos : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      0 < ∫ x, (P.winding (x, y) : ℝ)) :
    ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y) :=
  fun y hy hne => exists_winding_pos_of_crossSection_pos P y (hcpos y hy hne)

/-- **STEP A+B capstone — `winding_bdd` from the two remaining geometric inputs.**
Assume that at every generic height `y` there is an x-sorted (`Nodup`,
threshold-increasing) enumeration `L` of the spanning edges whose sign list
alternates (input **C**, no-nesting), and that whenever some spanning edge exists
the winding is positive somewhere on the line `{·.2 = y}` (input **B'**,
leftmost-crossing-is-down). Then `0 ≤ winding (x,y) ≤ 1` at every generic point —
exactly the `winding_bdd` hypothesis feeding
`winding_ae_mem_zero_one_of_winding_bdd`. -/
lemma winding_bdd_of_alternation_and_pos
    (halt : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      ∃ L : List (ZMod P.n), L.Nodup ∧ (∀ i, i ∈ L ↔ i ∈ P.spanningSet y) ∧
        L.Pairwise (fun i j => P.edgeThr y i < P.edgeThr y j) ∧
        AlternationCore.Alternates (L.map (P.edgeSign y)))
    (hposline : ∀ y, (∀ i, (toReal (P.vert i)).2 ≠ y) → (P.spanningSet y).Nonempty →
      ∃ x₀, 0 < P.winding (x₀, y)) :
    ∀ x y, (∀ i, (toReal (P.vert i)).2 ≠ y) →
      0 ≤ P.winding (x, y) ∧ P.winding (x, y) ≤ 1 := by
  intro x y hy
  obtain ⟨L, hnodup, hmem, hsorted, hLalt⟩ := halt y hy
  -- Case: no spanning edge at all ⟹ the list is empty ⟹ winding is 0.
  by_cases hempty : L.map (P.edgeSign y) = []
  · have hLempty : L = [] := by simpa using hempty
    have hSempty : P.spanningSet y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi; rw [← hmem i, hLempty] at hi; exact List.not_mem_nil hi
    have : P.winding (x, y) = 0 := by
      rw [winding_eq_sum_spanning P x y hy]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hSempty] at hi; exact absurd hi.1 (Finset.notMem_empty i)
    rw [this]; exact ⟨le_refl 0, zero_le_one⟩
  · -- Nonempty: get the positive witness, pin the head to `-1`, apply STEP A.
    have hSne : (P.spanningSet y).Nonempty := by
      rw [← Finset.coe_nonempty]
      have : L ≠ [] := by intro h; rw [h] at hempty; simp at hempty
      obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil L this
      exact ⟨i, (hmem i).mp hi⟩
    obtain ⟨x₀, hx₀⟩ := hposline y hy hSne
    have hhead := head_neg_of_winding_pos P y hy L hnodup hmem hsorted hLalt x₀ hx₀
    exact winding_bdd_of_xsorted_alternates P y hy L hnodup hmem hsorted hLalt hhead x


end Pick
