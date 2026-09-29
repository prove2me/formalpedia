-- Prove2me | solution 1 for WhichFactorWall.binEntropy_sub_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:34:02.775739+00:00
-- url     : https://prove2.me/submissions/ee8370dc-5f0d-4d71-8769-3261d513bfc1

import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
open WhichFactorWall Real Set in
theorem solution {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2⁻¹) :
    (q - p) * (log (1 - q) - log q) ≤ binEntropy q - binEntropy p := by
  rcases hpq.eq_or_lt with h | h
  · subst h
    simp
  · -- concavity: the derivative at the right endpoint is at most the chord slope
    have hq0 : q ≠ 0 := (lt_of_le_of_lt hp h).ne'
    have hq1 : q ≠ 1 := ne_of_lt (by linarith)
    have hd := strictConcave_binEntropy.concaveOn.deriv_le_slope
      ⟨hp, by linarith⟩ ⟨by linarith, by linarith⟩ h (differentiableAt_binEntropy hq0 hq1)
    rw [deriv_binEntropy, slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hd
    linarith [hd]
