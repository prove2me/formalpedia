-- Prove2me | solution 1 for ConcaveOn.le_add_deriv_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T03:01:22.922322+00:00
-- url     : https://prove2.me/submissions/20cdd5b4-55df-4e89-860e-8b07283c9bd5

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Set
open scoped Topology

theorem solution {s : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ s g) {x : ℝ} (hx : x ∈ s)
    (hdiff : DifferentiableAt ℝ g x) {y : ℝ} (hy : y ∈ s) :
    g y ≤ g x + deriv g x * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hslope := hg.deriv_le_slope hy hx hyx hdiff
    rw [slope] at hslope
    have hpos : 0 < x - y := sub_pos.mpr hyx
    have hs : deriv g x * (x - y) ≤ g x - g y := by
      apply (le_div_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    nlinarith
  · simp
  · have hslope := hg.slope_le_of_hasDerivAt hx hy hxy hdiff.hasDerivAt
    rw [slope] at hslope
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have hs : g y - g x ≤ deriv g x * (y - x) := by
      apply (div_le_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    linarith
