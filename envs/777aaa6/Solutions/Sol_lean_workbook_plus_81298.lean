-- Prove2me | solution 1 for lean_workbook_plus_81298
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:51:13.81107+00:00
-- url     : https://prove2.me/submissions/df8829b3-9ab8-4128-8007-29abc1c27e79

import Mathlib

theorem solution (a b : ℝ) : max a b = (a + b + |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring
