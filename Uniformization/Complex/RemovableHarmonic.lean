/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Rado.Surface.Germs

/-!
# Removable singularity for bounded harmonic functions (Anghel–Stan Lemma 8)

A harmonic function on a punctured disk that is bounded near the puncture
extends harmonically across the puncture.

Proof plan (planar, Mathlib-friendly; no multivalued arguments):
write `u = Re F` locally (`Rado.exists_conjugate` at `X := ℂ`), so
`h := F'` glues to a global holomorphic function on the punctured ball
(conjugates differ by additive constants). The interior gradient estimate
`‖h z‖ ≤ C·M/‖z − c‖` (from the Poisson/Schwarz representation on
`ball z (‖z − c‖/2)`) makes `(z − c)·h z` bounded, hence removable
(`Complex.differentiableOn_update_limUnder_of_bddAbove`); write
`(z − c)·h z = k z` with `k` holomorphic, `κ := k c`. Then `κ ∈ ℝ`
(its imaginary part is `(2π)⁻¹·∮ du = 0`), and
`u − κ·log‖z − c‖` has `∂`-derivative `(k z − κ)/(z − c)` holomorphic on the
full ball, hence equals `Re` of its primitive up to a constant, hence extends
harmonically. Boundedness of `u` forces `κ = 0`.
-/

open Set Metric InnerProductSpace

namespace Uniformization

/-- **Removable singularity for bounded harmonic functions** (Anghel–Stan Lemma 8).
A harmonic function on a punctured ball, bounded near the puncture, extends
harmonically across the puncture. -/
theorem exists_harmonicOnNhd_extension_of_bounded {c : ℂ} {R : ℝ} (hR : 0 < R)
    {u : ℂ → ℝ} {M : ℝ} (hu : HarmonicOnNhd u (ball c R \ {c}))
    (hbd : ∀ z ∈ ball c R \ {c}, |u z| ≤ M) :
    ∃ v : ℂ → ℝ, HarmonicOnNhd v (ball c R) ∧ EqOn v u (ball c R \ {c}) := by
  sorry

end Uniformization
