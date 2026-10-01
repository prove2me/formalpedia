-- Prove2me | solution 1 for BookSixth.alltime_line_piecewise_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T18:16:45.526331+00:00
-- url     : https://prove2.me/submissions/d109bea3-683f-4102-8021-ec01a81d896e

import Mathlib

theorem solution (a b L : ℝ) (hL : L = b - a - 2)
    (hLb : 0 < b - a - 2) (t : ℝ) :
    (0 < (1 - max 0 (min t 1)) + max 0 (min t 1) / L) ∧
    ((a + 1 - max 0 (min t 1) * a)
        + (b - 1 - (a + 1)) * ((1 - max 0 (min t 1)) + max 0 (min t 1) / L)
      = b - 1 + max 0 (min t 1) * (3 - b)) ∧
    (max 0 (min t 1) * a + (a + 1 - max 0 (min t 1) * a)
        = a + 1) := by
  subst L
  have hT0 : 0 ≤ max 0 (min t 1) := le_max_left _ _
  have hT1 : max 0 (min t 1) ≤ 1 := max_le_iff.mpr ⟨by norm_num, min_le_right t 1⟩
  have hone : 0 ≤ 1 - max 0 (min t 1) := by linarith
  have hne : b - a - 2 ≠ 0 := ne_of_gt hLb
  have hkey : (1 - max 0 (min t 1)) + max 0 (min t 1) / (b - a - 2)
      = ((1 - max 0 (min t 1)) * (b - a - 2) + max 0 (min t 1)) / (b - a - 2) := by
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hkey]
    have hnum : 0 < (1 - max 0 (min t 1)) * (b - a - 2) + max 0 (min t 1) := by
      nlinarith [mul_nonneg hone (le_of_lt hLb)]
    exact div_pos hnum hLb
  · rw [hkey]
    field_simp [hne]
    ring
  · ring
