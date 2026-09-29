-- Prove2me | solution 1 for lean_workbook_plus_16719
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:49.159704+00:00
-- url     : https://prove2.me/submissions/c1d44742-dc68-47ea-b478-831315f95e9d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : |a * 0 ^ 2 + b * 0 + c| = |c| := by
  norm_num
