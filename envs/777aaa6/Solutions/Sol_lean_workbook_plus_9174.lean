-- Prove2me | solution 1 for lean_workbook_plus_9174
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:50.864031+00:00
-- url     : https://prove2.me/submissions/4abadc8a-805c-424c-8a59-d0713ba9fb4f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ((2 : ℝ) * 15 / 24 * (9 / 23)) = 45 / 92 := by
  norm_num
