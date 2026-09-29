-- Prove2me | solution 1 for lean_workbook_plus_4329
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:22.06476+00:00
-- url     : https://prove2.me/submissions/a8f43ab3-c9ea-42fa-baf0-55b0a79ecc38

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℤ) : (a + 1) ^ 2 - (a + 2) ^ 2 - (a + 3) ^ 2 + a ^ 2 = -8 * a - 12 := by
  (intros; linarith)
