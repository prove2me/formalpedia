-- Prove2me | solution 1 for lean_workbook_plus_33183
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:27.571898+00:00
-- url     : https://prove2.me/submissions/9e49152e-316a-44c3-8dff-c6bc7d80181d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ (x y : ℝ), x = y → x - y = 0 := by
  norm_num
