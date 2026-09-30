-- Prove2me | solution 1 for lean_workbook_plus_62965
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:37:29.935101+00:00
-- url     : https://prove2.me/submissions/4fdc6263-1163-4cfc-9c84-994134caf2e6

import Mathlib

noncomputable def five_shift_sum (x : ℝ) : ℝ :=
  |x+1| + |x+5| + |x+14| + |x+97| + |x+1920|

theorem sharp_bound (x : ℝ) : 2011 + |x+14| ≤ five_shift_sum x := by
  dsimp [five_shift_sum]
  linarith only [neg_le_abs (x+1), le_abs_self (x+1920),
    neg_le_abs (x+5), le_abs_self (x+97)]

theorem minimum_iff (x : ℝ) : five_shift_sum x = 2011 ↔ x = -14 := by
  constructor
  · intro h
    have hz : |x+14| = 0 := by linarith only [sharp_bound x, h, abs_nonneg (x+14)]
    have := abs_eq_zero.mp hz
    linarith
  · rintro rfl
    unfold five_shift_sum
    rw [abs_of_nonpos (by norm_num : (-14:ℝ)+1 ≤ 0),
      abs_of_nonpos (by norm_num : (-14:ℝ)+5 ≤ 0),
      abs_of_nonneg (by norm_num : 0 ≤ (-14:ℝ)+14),
      abs_of_nonneg (by norm_num : 0 ≤ (-14:ℝ)+97),
      abs_of_nonneg (by norm_num : 0 ≤ (-14:ℝ)+1920)]
    ring

theorem solution (x : ℝ) :
    2011 ≤ abs (x+1) + abs (x+5) + abs (x+14) + abs (x+97) + abs (x+1920) := by
  have h := sharp_bound x
  dsimp [five_shift_sum] at h
  linarith only [h, abs_nonneg (x+14)]
