-- Prove2me | solution 1 for lean_workbook_plus_79823
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:59:59.602385+00:00
-- url     : https://prove2.me/submissions/1ac78cea-fbb3-4fcf-ac49-22818dbc97cd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 >= (x + y + z) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
