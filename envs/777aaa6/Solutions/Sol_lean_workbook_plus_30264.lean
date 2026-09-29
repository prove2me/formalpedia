-- Prove2me | solution 1 for lean_workbook_plus_30264
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:18.106132+00:00
-- url     : https://prove2.me/submissions/566b5aae-ca68-4b88-9526-bd992e321a85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  (intros; linarith)
