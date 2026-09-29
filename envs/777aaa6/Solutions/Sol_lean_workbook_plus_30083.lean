-- Prove2me | solution 1 for lean_workbook_plus_30083
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:41.419831+00:00
-- url     : https://prove2.me/submissions/06e09f82-15a1-47a2-a323-482b77983093

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ 0) : 1 / (1 / x) = x := by
  norm_num
