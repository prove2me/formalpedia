-- Prove2me | solution 1 for lean_workbook_plus_48903
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:24.255077+00:00
-- url     : https://prove2.me/submissions/270967ee-11b6-4403-b6a9-f29597fd6b96

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 7 * 11 * 13 * 1003 - 3 * 17 * 59 * 331 = 8024) : 7 * 11 * 13 * 1003 - 3 * 17 * 59 * 331 = 8024 := by
  norm_num
